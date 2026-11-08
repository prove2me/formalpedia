-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_7_5
-- name    : ExactPatternStream.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:36.637781+00:00
-- url     : https://prove2.me/theorems/9ad4ecb7-cd68-4507-b6b8-499cccc8c858
-- title:
--   Lemma 7.5 — $\mathrm{Sum}_k$: accuracy and $O((k+\log\log N)\log r)$ bits
-- statement:
--   For every $k\ge1$, there is a deterministic one-pass algorithm $\mathrm{Sum}_k$ that, on $r\ge2$ precision-$k$ counters $z_1,\dots,z_r$, returns a precision-$k$ counter $z$ with
--   $$\mathrm{val}(z)\le\sum_{j=1}^r\mathrm{val}(z_j)\le\exp(\lceil\log_2r\rceil2^{-k})\mathrm{val}(z).$$
--   If $\mathrm{val}(z_j)\le x_j\le\exp(\theta)\mathrm{val}(z_j)$ for every $j$, then $\mathrm{val}(z)\le\sum_jx_j\le\exp(\theta+\lceil\log_2r\rceil2^{-k})\mathrm{val}(z)$. If $\sum_j\mathrm{val}(z_j)\le N$ with $N\ge4$, it uses $O((k+\log\log N)\log r)$ working bits.
--
--   This keeps a node's approximate weight in its label at a small cost in bits.
--
--   Differences from the source:
--   - reading: "deterministic one-pass algorithm … uses $O((k+\log\log N)\log r)$ working bits" → `sumK` for the accuracy clauses; for the space clause, one finite-state `Evaluator` per $(k,r,N)$ with that many state bits, one update per counter; reason: the source counts working space and does not fix a machine at this level; the goal's single program is the job of Lemma 9.2
--   - encoding: $x_j$ unspecified → $x_j$ real numbers; reason: the use has integers, which are real
--   - encoding: $O(\cdot)$ → one absolute $K$ before all variables, with $\log_2$; reason: the same bounds up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.5, p.20 (PDF 21)

import Mathlib
import Definitions.Def_ExactPatternStream_LinearMaps
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_HashFamily
import Definitions.Def_ExactPatternStream_Counters

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.5, p.20 (PDF 21).

`Sum_k` on `r ≥ 2` precision-`k` counters returns a precision-`k` counter `z` with `val(z) ≤ Σ val(z_j) ≤ exp(⌈log₂ r⌉ 2^{-k}) val(z)`; if `val(z_j) ≤ x_j ≤ exp(θ) val(z_j)` for every `j`, then `val(z) ≤ Σ x_j ≤ exp(θ + ⌈log₂ r⌉ 2^{-k}) val(z)`; and if `Σ val(z_j) ≤ N`, `N ≥ 4`, it uses `O((k + log log N) log r)` working bits.

**Formalization Note.** `Sum_k` is `sumK`, the merge of the proof. The space clause is a `reading`: for each `(k, r, N)`, one finite-state `Evaluator` with a bounded number of state bits, one update per counter, whose output is `sumK k` on every admissible input. `O(·)` is one absolute `K` before `k, r, N`, and `log = log₂`. `x_j` are real numbers. -/
theorem lemma_7_5 : ∃ K : ℝ, ∀ k : ℕ, 1 ≤ k →
    (∀ zs : List (ℕ × ℕ), 2 ≤ zs.length → (∀ z ∈ zs, IsCounter k z) →
      IsCounter k (sumK k zs) ∧
      val (sumK k zs) ≤ (zs.map val).sum ∧
      ((zs.map val).sum : ℝ) ≤
        Real.exp ((Nat.clog 2 zs.length : ℝ) * (2 : ℝ)⁻¹ ^ k) * (val (sumK k zs) : ℝ) ∧
      ∀ (xs : List ℝ) (θ : ℝ),
        List.Forall₂ (fun z x => (val z : ℝ) ≤ x ∧ x ≤ Real.exp θ * (val z : ℝ)) zs xs →
        (val (sumK k zs) : ℝ) ≤ xs.sum ∧
          xs.sum ≤ Real.exp (θ + (Nat.clog 2 zs.length : ℝ) * (2 : ℝ)⁻¹ ^ k) *
            (val (sumK k zs) : ℝ)) ∧
    ∀ r N : ℕ, 2 ≤ r → 4 ≤ N →
      ∃ ev : Evaluator Unit (ℕ × ℕ) (ℕ × ℕ),
        (ev.bits : ℝ) ≤ K * ((k : ℝ) + Real.logb 2 (Real.logb 2 N)) * Real.logb 2 r ∧
        ∀ zs : List (ℕ × ℕ), zs.length = r → (∀ z ∈ zs, IsCounter k z) →
          (zs.map val).sum ≤ N → ev.run () zs = sumK k zs := by sorry

end ExactPatternStream
