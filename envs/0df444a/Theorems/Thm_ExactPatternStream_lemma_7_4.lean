-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_7_4
-- name    : ExactPatternStream.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:22.603937+00:00
-- url     : https://prove2.me/theorems/8c4e8a42-284b-4cc2-9e25-3fb9db2008cb
-- title:
--   Lemma 7.4 — the seeded family $\mathcal H_{L,b}$: seed, streaming evaluation, inclusion, error
-- statement:
--   For all positive integers $L,b$, the explicit seeded family $\mathcal H_{L,b}$ of maps $h:\{0,1\}^L\to\{0,1\}^b$ satisfies:
--
--   1. its seed length is $O(b\log(2+L/b))$ bits;
--   2. every $h\in\mathcal H_{L,b}$ can be evaluated as its input bits arrive by a one-pass streaming algorithm using $O(b\log(2+L/b))$ bits of working space;
--   3. extended coordinatewise to strings of $L$-bit symbols, for fixed $P\in(\{0,1\}^L)^m$, $T\in(\{0,1\}^L)^n$, $1\le m\le n$, every $h$ satisfies $\mathrm{Occ}(P,T)\subseteq\mathrm{Occ}(h(P),h(T))$;
--   4. and a uniformly random seed satisfies
--   $$\Pr\big[\mathrm{Occ}(P,T)\ne\mathrm{Occ}(h(P),h(T))\big]=O\Big(\frac nm\cdot\frac{\log^2(2+mL/b)}{2^{b/2}}\Big).$$
--   This is the fingerprint that replaces $\Omega(\log m)$-bit Karp–Rabin hashes on the lower levels.
--
--   Differences from the source:
--   - reading: "can be evaluated … by a one-pass streaming algorithm using $O(b\log(2+L/b))$ bits of working space" → one finite-state `Evaluator` per $(L,b)$, started from the seed, with that many state bits and one update per input bit; reason: the source counts working space and does not fix a machine at this level; the goal's single program is the job of Lemma 9.2
--   - encoding: a family defined by its proof, with a constant map when $L>b$, $b\le3$ → `hashEval`, with the constant $0^b$; reason: the statement says "explicit" and the proof defines the family
--   - encoding: $\{0,1\}^L$ → `List Bool` with a length hypothesis; reason: the same strings
--   - encoding: $O(\cdot)$ → one absolute $K$ before all variables, with $\log_2$; reason: the same bounds up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.4, p.19 (PDF 20)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_LinearMaps
import Definitions.Def_ExactPatternStream_HashFamily

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.4, p.19 (PDF 20).

For all positive `L, b`, the explicit family `H_{L,b}` of maps `{0,1}^L → {0,1}^b` has seed length `O(b log(2 + L/b))`; its maps are evaluated one bit at a time in `O(b log(2 + L/b))` bits; every `h` satisfies `Occ(P, T) ⊆ Occ(h(P), h(T))`; and a uniform seed has `Pr[Occ(P, T) ≠ Occ(h(P), h(T))] = O((n/m) log²(2 + mL/b)/2^{b/2})`.

**Formalization Note.** The family is the one defined in the proof (`hashEval`, `HSeed`). The seed length is `log₂` of the size of the seed space. Streaming evaluation is a `reading`: one finite-state `Evaluator` per `(L, b)`, with a bounded number of state bits, started from the seed, so the seed sits in the counted state, and one update per input bit. `O(·)` is one absolute `K` before `L, b`. Bit strings of length `L` are `List Bool` with a length hypothesis. -/
theorem lemma_7_4 : ∃ K : ℝ, ∀ L b : ℕ, 0 < L → 0 < b →
    Real.logb 2 (Fintype.card (HSeed L b) : ℝ) ≤ K * b * Real.logb 2 (2 + (L : ℝ) / b) ∧
    (∃ ev : Evaluator (HSeed L b) Bool (List Bool),
      (ev.bits : ℝ) ≤ K * b * Real.logb 2 (2 + (L : ℝ) / b) ∧
        ∀ (s : HSeed L b) (x : List Bool), x.length = L → ev.run s x = hashEval L b s x) ∧
    (∀ (s : HSeed L b) (x : List Bool), x.length = L → (hashEval L b s x).length = b) ∧
    ∀ P T : List (List Bool), 1 ≤ P.length → P.length ≤ T.length →
      (∀ x ∈ P, x.length = L) → (∀ x ∈ T, x.length = L) →
      (∀ s : HSeed L b, occ P T ⊆ occ (P.map (hashEval L b s)) (T.map (hashEval L b s))) ∧
      unifProb (fun s : HSeed L b =>
          occ P T ≠ occ (P.map (hashEval L b s)) (T.map (hashEval L b s))) ≤
        K * ((T.length : ℝ) / P.length) *
            Real.logb 2 (2 + (P.length : ℝ) * L / b) ^ 2 / (2 : ℝ) ^ ((b : ℝ) / 2) := by sorry

end ExactPatternStream
