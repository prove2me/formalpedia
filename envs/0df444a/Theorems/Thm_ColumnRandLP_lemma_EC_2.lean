-- Prove2me | Theorems.Thm_ColumnRandLP_lemma_EC_2
-- name    : ColumnRandLP.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:23:59.960358+00:00
-- url     : https://prove2.me/theorems/9b282f8b-59d7-434c-9c0b-aef7b96ab3a0
-- title:
--   Lemma EC.2 — the mean of $K$ i.i.d. vectors with $\|w_k\|_\infty\le C$ is within $\frac{mC}{\sqrt K}(1+\sqrt{2\log(1/\delta)})$ in $\ell_1$ w.p. $\ge 1-\delta$
-- statement:
--   Let $w_1,\dots,w_K$ ($K\ge1$) be independent and identically distributed random vectors of size $m$ such that $\|w_k\|_\infty\le C$ for $k=1,\dots,K$, and let $\bar w=\frac1K\sum_{k=1}^K w_k$. Then for every $\delta\in(0,1)$, with probability at least $1-\delta$,
--   $$
--   \|\bar w-\mathbb E[\bar w]\|_1\le\frac{mC}{\sqrt K}\Big(1+\sqrt{2\log\tfrac1\delta}\Big).
--   $$
--
--   The paper applies it to $b_k=Aw_k$ in Step 2 of Proposition EC.3 to bound $\|b'-b\|_1$, the infeasibility of the sparsified solution.
--
--   **Formalization Note** The vectors are measurable maps from a probability space into `Fin m → ℝ`; independence is `iIndepFun` and identical distribution is pairwise `IdentDistrib`. $\|w_k\|_\infty\le C$ is written entrywise ($|w_{k,i}|\le C$ for every $i$ and every sample point) and $\|\cdot\|_1$ is the explicit sum `l1Norm`. $\mathbb E[\bar w]$ is the Bochner integral. $\log$ is natural.
--
--   Differences from the source:
--   - encoding: i.i.d. random vectors of size m with ‖w_k‖∞ ≤ C → measurable maps on a probability space into Fin m → ℝ, iIndepFun plus pairwise IdentDistrib, |w_k i| ≤ C for every i at every sample point; reason: the standard measure-theoretic reading; the entrywise bound is the definition of ‖·‖∞
--   - reading: K, the number of vectors → 1 ≤ K; reason: the bound contains 1/√K and averages K vectors
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, Lemma EC.2, p.ec7

import Mathlib
import Definitions.Def_ColumnRandLP_Norms

open MeasureTheory ProbabilityTheory

namespace ColumnRandLP

/-- **Lemma EC.2** (Akchen–Mišić, arXiv:2007.10461v5, Lemma EC.2, p.ec7). Let `w₁, …, w_K` be
i.i.d. random vectors of size `m` with `‖w_k‖∞ ≤ C` for every `k`, and `w̄ = (1/K) ∑_k w_k`.
For every `δ ∈ (0,1)`, with probability at least `1 − δ`,
`‖w̄ − E[w̄]‖₁ ≤ mC/√K · (1 + √(2 log(1/δ)))`.

**Formalization Note** The vectors are measurable maps `Ω → (Fin m → ℝ)` on a probability space;
"i.i.d." is `iIndepFun` with pairwise `IdentDistrib`. `‖w_k‖∞ ≤ C` is written entrywise
(`|w_k(ω)_i| ≤ C` for all `i` and all `ω`), and `‖·‖₁` is the explicit sum `l1Norm`. `E[w̄]` is
the Bochner integral (the vectors are bounded, hence integrable). `K ≥ 1`; `log` is natural. -/
theorem lemma_EC_2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m K : ℕ} (hK : 1 ≤ K) (w : Fin K → Ω → (Fin m → ℝ))
    (hmeas : ∀ k, Measurable (w k)) (hind : iIndepFun w μ)
    (hident : ∀ k k', IdentDistrib (w k) (w k') μ μ)
    (C : ℝ) (hbound : ∀ k ω i, |w k ω i| ≤ C) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      μ {ω | l1Norm ((1 / (K : ℝ)) • ∑ k, w k ω - ∫ ω', (1 / (K : ℝ)) • ∑ k, w k ω' ∂μ) ≤
        (m : ℝ) * C / Real.sqrt K * (1 + Real.sqrt (2 * Real.log (1 / δ)))} := by sorry

end ColumnRandLP
