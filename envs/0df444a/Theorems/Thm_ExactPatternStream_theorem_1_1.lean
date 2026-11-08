-- Prove2me | Theorems.Thm_ExactPatternStream_theorem_1_1
-- name    : ExactPatternStream.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:49.143227+00:00
-- url     : https://prove2.me/theorems/fd6cc476-aeb6-4bf2-89a6-92adc96f6f6d
-- title:
--   Theorem 1.1 — for $n\le2m$, $O(\log n\log\log n)$ bits and one-sided error at most $1/\log n$
-- statement:
--   Exact Pattern Matching with $n\le2m$ can be solved by a streaming algorithm with space complexity $O(\log n\log\log n)$ bits and one-sided error probability at most $1/\log n$.
--
--   Precisely: for every $k$ there are one program $Q$ and constants $c_w,K$ such that, for every alphabet size $\sigma$ and all $P\in\Sigma^m$, $T\in\Sigma^n$ with $1\le m\le n\le2m$, $n\ge3$, $\sigma\le n^k$, with word size $w=c_w\ell(n)$:
--
--   1. **Space.** At most $K\log_2n\log_2\log_2n$ bits are used, on every coin tape at every step.
--   2. **On time.** No answer comes before $T[m-1]$ is processed; then exactly one for each character, before the next is delivered.
--   3. **Completion.** With probability $1$, every character is processed.
--   4. **One-sided.** On every coin tape, whenever $P=T(i-m\,.\,.\,i]$, the answer for $i$ is YES.
--   5. **Correct.** With probability at least $1-1/\log_2n$, all answers are correct together.
--
--   This improves the $O(\log^2n)$ bits of Porat–Porat and Breslauer–Galil for $n\le2m$, against an $\Omega(\log n)$ lower bound.
--
--   Differences from the source:
--   - reading: "a streaming algorithm" and "space complexity", with no named model → one `DynBrooks.Program`, word size $w=c_w\ell(n)$, $w$ bits per cell ever written, with a coin tape it cannot rewind; reason: the authors' disclosure says an uncharged seed was their earlier, weaker result, so every kept random bit must be charged, and a finite-state automaton per input size would hide workspace in its transition function
--   - generalization: $n\ge m\ge C$, with $m<C$ solved "deterministically" (footnote 1) → every $1\le m\le n\le2m$ with $n\ge3$; reason: it includes the footnote's case; $n=1,2$ are excluded only because $1/\log1$ is undefined and $\log2\cdot\log\log2=0$
--   - encoding: $|\Sigma|\le n^{O(1)}$, $O(\cdot)$ → $\forall k$, then $Q,c_w,K$, then the input; $\log=\log_2$; reason: later constants would admit storing the input
--   - reading: $\log$ in the error and in the space → $\log_2$; reason: $1/\log_2n$ is the strongest bound among bases $\ge2$, and §7 uses base $2$
--   - encoding: rejection sampling, "at most two trials on average" → the run completes almost surely, a separate clause; reason: a sampler with no worst-case bound has non-terminating runs on a null set of tapes
--   - encoding: answers YES/NO, $\Sigma=\{1,\dots,|\Sigma|\}$, known $n,m,|\Sigma|$ → words $1$/$0$, symbols $a+1$ for $a\in$ `Fin σ`, and $n,m,\sigma$ as the first words read; reason: the same task
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Theorem 1.1, p.2 (PDF 3), with the task on p.1 (PDF 2)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_StreamRun

open MeasureTheory

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Theorem 1.1, p.2 (PDF 3), with the task of §1, p.1 (PDF 2).

Exact Pattern Matching with `n ≤ 2m` is solved by one streaming program with `O(log n log log n)` bits and one-sided error probability at most `1/log n`: for every polynomial alphabet bound, for all `1 ≤ m ≤ n ≤ 2m` with `n ≥ 3`, (1) charged space is at most `K log₂ n log₂ log₂ n` on every tape at every step; (2) no answer comes before `T[m-1]` is processed, and then one per character, before the next is delivered; (3) the run almost surely completes; (4) at every occurrence, on every tape, the answer is YES; (5) all answers are correct together with probability at least `1 - 1/log₂ n`.

**Formalization Note.** The paper names no machine. A program is a `DynBrooks.Program`: it cannot rewind its coin tape, so every random bit it keeps is in a charged cell. Word size `w = cw · ℓ(n)`, space `w · |cells ever written|`. `Q, cw, K` come after `k` and **before** the input. `n, m, |Σ|` are delivered as the first words; symbols are `1..σ` in the stream; YES is `1`, NO is `0`. `P, T` are fixed before the coins. A hypothesis that symbols fit in a word is not needed: `σ ≤ n^k` and `cw` follows `k`. A word of `0` bits cannot output `1`, so `cw = 0` fails (4). Rejection sampling has no worst-case bound, so runs may not complete on a null set of tapes, which is clause (3). `n ≥ 3` is where the printed bounds make sense: `1/log₂ 1` is undefined, and `log₂ 2 · log₂ log₂ 2 = 0`. Time is not bounded: Theorem 1.1 has no time clause. -/
theorem theorem_1_1 : ∀ k : ℕ, ∃ (Q : DynBrooks.Program) (cw K : ℕ),
    ∀ (σ : ℕ) (P T : List (Fin σ)),
    1 ≤ P.length → P.length ≤ T.length → T.length ≤ 2 * P.length → 3 ≤ T.length →
    σ ≤ T.length ^ k →
    let m := P.length
    let n := T.length
    let w := cw * ell n
    let B : ℝ := (K : ℝ) * Real.logb 2 n * Real.logb 2 (Real.logb 2 n)
    (∀ (ω : ℕ → BitVec w) (t : ℕ),
      (spaceBits w (DynBrooks.run Q ω (startConfig w P T) t) : ℝ) ≤ B) ∧
    (∀ (ω : ℕ → BitVec w) (j : ℕ) (c : DynBrooks.Config w), j < m + n →
      streamState Q P T ω j = some c → ∀ t : ℕ,
        (spaceBits w (DynBrooks.run Q ω (DynBrooks.feed c [(streamWords P T).getD j 0]) t) : ℝ) ≤ B) ∧
    (∀ (ω : ℕ → BitVec w) (j : ℕ) (c : DynBrooks.Config w), j ≤ m + n →
      streamState Q P T ω j = some c → c.output.length = (j + 1) - 2 * m) ∧
    ProbAtLeast (DynBrooks.coinMeasure w)
      {ω | ∀ j ≤ m + n, (streamState Q P T ω j).isSome} 1 ∧
    (∀ (ω : ℕ → BitVec w) (i : ℕ) (c : DynBrooks.Config w), m ≤ i + 1 → i < n → EndsAt P T i →
      streamState Q P T ω (m + i + 1) = some c → c.output[i + 1 - m]? = some 1) ∧
    ProbAtLeast (DynBrooks.coinMeasure w)
      {ω | ∃ c, streamState Q P T ω (m + n) = some c ∧ c.output = truthList P T}
      (ENNReal.ofReal (1 - 1 / Real.logb 2 n)) := by sorry

end ExactPatternStream
