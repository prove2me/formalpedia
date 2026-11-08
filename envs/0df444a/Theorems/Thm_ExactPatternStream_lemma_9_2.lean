-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_9_2
-- name    : ExactPatternStream.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:39.065347+00:00
-- url     : https://prove2.me/theorems/8fcd5899-f52c-4e42-995e-62db9bd66c61
-- title:
--   Lemma 9.2 — one program implements Algorithms 1 and 2 in $O(\log n\log\log n)$ bits
-- statement:
--   For $m\le n\le2m$, the procedure of §9 implements the matching answers of Algorithms 1 and 2 in one pass over each input, reporting each answer before the next input character is read, using $O(\log n\log\log n)$ bits.
--
--   Precisely: for every $k$ there are one program $Q$, constants $c_w,K$ and primes $p_R(n,m,\sigma)>2^{4\mathcal L}$ with $\log_2p_R\le K\log_2n$ such that, for all $1\le m\le n\le2m$, $n\ge3$, $\sigma\le n^k$:
--
--   1. space is at most $K\log_2n\log_2\log_2n$ bits on every tape at every step;
--   2. no answer comes before $T[m-1]$ is processed, then one answer per character, before the next is delivered;
--   3. the run almost surely completes;
--   4. there is a measurable map $\Phi$ from tapes to $(\omega,a_R)$ with the uniform law, such that a tape whose run completes outputs, for $m\le t\le n$, YES at raw position $t-1$ exactly when $t-m\in M$, for the $M$ of $\mathrm{Match}(P,T)$ at $\Phi$ of the tape;
--   5. on every tape, the answers so far are a prefix of those of $\mathrm{Match}(P,T)$ at some seeds.
--
--   With Lemmas 5.2 and 8.5, this gives Theorem 1.1. Only the implementation is here, no new probability.
--
--   Differences from the source:
--   - reading: "a streaming algorithm" and "space complexity", with no named model → one `DynBrooks.Program`, word size $w=c_w\ell(n)$, $w$ bits per cell ever written, with a coin tape it cannot rewind; reason: the authors' disclosure says an uncharged seed was their earlier, weaker result, so every kept random bit must be charged, and a finite-state automaton per input size would hide workspace in its transition function
--   - reading: "implements the matching answers of Algorithms 1 and 2" → a measurable coupling $\Phi$ of tapes with the uniform seeds, and on partial runs a prefix of the answers at some seeds; reason: the seeds are read from the coins, and the prefix clause carries the "always outputs YES" of p.1 to every tape, including those that never finish
--   - generalization: $n\ge m\ge C$, with $m<C$ solved "deterministically" (footnote 1) → every $1\le m\le n\le2m$ with $n\ge3$; reason: it includes the footnote's case; $n=1,2$ are excluded only because $1/\log1$ is undefined and $\log2\cdot\log\log2=0$
--   - encoding: $|\Sigma|\le n^{O(1)}$, $O(\cdot)$ → $\forall k$, then $Q,c_w,K$, then the input; $\log=\log_2$; reason: later constants would admit storing the input
--   - encoding: rejection sampling, "at most two trials on average" → the run completes almost surely, a separate clause; reason: a sampler with no worst-case bound has non-terminating runs on a null set of tapes
--   - encoding: answers YES/NO, $\Sigma=\{1,\dots,|\Sigma|\}$, known $n,m,|\Sigma|$ → words $1$/$0$, symbols $a+1$ for $a\in$ `Fin σ`, and $n,m,\sigma$ as the first words read; reason: the same task
--   - encoding: $H_i$ sampled once level $i$ is known → one independent uniform block per level, read through a prefix (`Seeds`); reason: the same law: a prefix of an independent uniform block is uniform and independent of the lower levels
--   - encoding: "fix any injective" codes $\mathrm{code}_0$, $\mathrm{code}_{\mathrm{cnt}}$ → the fixed binary codes of `SeededHash`; reason: the source fixes one code, and nothing depends on the choice
--   - encoding: "Choose a prime $p_R>2^{4\mathcal L}$ with $\log p_R=O(\log m)$" → $p_R$ a function of $(n,m,\sigma)$ chosen with $Q$, with $\log_2p_R\le K\log_2n$; reason: $n\le2m$, so the two logarithms agree up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 9.2, p.29 (PDF 30), with the procedure of §9, pp.27–29 (PDF 28–30)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build
import Definitions.Def_ExactPatternStream_LinearMaps
import Definitions.Def_ExactPatternStream_HashFamily
import Definitions.Def_ExactPatternStream_Counters
import Definitions.Def_ExactPatternStream_SeededHash
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_ExactPatternStream_StreamRun

open MeasureTheory

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 9.2, p.29 (PDF 30), with the procedure of §9.

For `m ≤ n ≤ 2m`, one program implements the matching answers of Algorithms 1 and 2 in one pass, reports each answer before the next character is read, and uses `O(log n log log n)` bits. Its seeds come from its coin tape: there is a measurable map `Φ` from tapes to `(ω, a_R)` whose law is the uniform one, and a run's answers are those of `Match(P, T)` at `Φ` of its tape.

**Formalization Note.** The machine is `DynBrooks.Program`, as in the goal, with word size `cw · ℓ(n)`; `|Σ| ≤ n^{O(1)}` is `∀ k`; `Q, cw, K, p_R` come before the input (the program chooses `p_R`, with `log p_R = O(log m)`, p.22). Space is for **every** tape at **every** step. A tape on which rejection sampling never ends has no completed state; these form a null set. The last clause, on partial runs, says the answers so far agree with `Match` at some seeds, for **every** tape: this is what makes the error one-sided on every tape, as `Match`'s completeness holds at all seeds. -/
theorem lemma_9_2 : ∀ k : ℕ, ∃ (Q : DynBrooks.Program) (cw K : ℕ) (pR : ℕ → ℕ → ℕ → Nat.Primes),
    ∀ (σ : ℕ) (P T : List (Fin σ)),
    1 ≤ P.length → P.length ≤ T.length → T.length ≤ 2 * P.length → 3 ≤ T.length →
    σ ≤ T.length ^ k →
    let m := P.length
    let n := T.length
    let w := cw * ell n
    let B : ℝ := (K : ℝ) * Real.logb 2 n * Real.logb 2 (Real.logb 2 n)
    let p : ℕ := pR n m σ
    2 ^ (4 * bigL σ m) < p ∧ Real.logb 2 p ≤ (K : ℝ) * Real.logb 2 n ∧
    (∀ (ω : ℕ → BitVec w) (t : ℕ),
      (spaceBits w (DynBrooks.run Q ω (startConfig w P T) t) : ℝ) ≤ B) ∧
    (∀ (ω : ℕ → BitVec w) (j : ℕ) (c : DynBrooks.Config w), j < m + n →
      streamState Q P T ω j = some c → ∀ t : ℕ,
        (spaceBits w (DynBrooks.run Q ω (DynBrooks.feed c [(streamWords P T).getD j 0]) t) : ℝ) ≤ B) ∧
    (∀ (ω : ℕ → BitVec w) (j : ℕ) (c : DynBrooks.Config w), j ≤ m + n →
      streamState Q P T ω j = some c → c.output.length = (j + 1) - 2 * m) ∧
    ProbAtLeast (DynBrooks.coinMeasure w)
      {ω | ∀ j ≤ m + n, (streamState Q P T ω j).isSome} 1 ∧
    ∃ Φ : (ℕ → BitVec w) → Seeds σ m × ZMod (pR n m σ : ℕ),
      (∀ E : Set (Seeds σ m × ZMod (pR n m σ : ℕ)), MeasurableSet (Φ ⁻¹' E) ∧
        DynBrooks.coinMeasure w (Φ ⁻¹' E) =
          ENNReal.ofReal (unifProb fun s => s ∈ E)) ∧
      (∀ (ω : ℕ → BitVec w) (c : DynBrooks.Config w), streamState Q P T ω (m + n) = some c →
        c.output = answersOf P T (seededMatch P T (Φ ω))) ∧
      ∀ (ω : ℕ → BitVec w) (j : ℕ) (c : DynBrooks.Config w), j ≤ m + n →
        streamState Q P T ω j = some c →
        ∃ s : Seeds σ m × ZMod (pR n m σ : ℕ), c.output <+: answersOf P T (seededMatch P T s) := by sorry

end ExactPatternStream
