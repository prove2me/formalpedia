-- Prove2me | Theorems.Thm_ColumnRandLP_lemma_EC_1
-- name    : ColumnRandLP.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:23:22.97354+00:00
-- url     : https://prove2.me/theorems/b51aa82e-ceb3-44f5-b2fb-ee898b67f914
-- title:
--   Lemma EC.1 — the mean of $K$ i.i.d. vectors with $\|w_k\|_2\le C$ is within $\frac{C}{\sqrt K}(1+\sqrt{2\log(1/\delta)})$ of its expectation w.p. $\ge 1-\delta$
-- statement:
--   Let $w_1,\dots,w_K$ ($K\ge1$) be independent and identically distributed random vectors in $\mathbb R^d$ such that $\|w_k\|_2\le C$ for $k=1,\dots,K$, and let $\bar w=\frac1K\sum_{k=1}^K w_k$. Then for every $\delta\in(0,1)$, with probability at least $1-\delta$,
--   $$
--   \|\bar w-\mathbb E[\bar w]\|_2\le\frac{C}{\sqrt K}\Big(1+\sqrt{2\log\tfrac1\delta}\Big).
--   $$
--
--   This is the vector concentration inequality of Rahimi and Recht (2009, Lemma 4), which the paper uses to show that the importance-weighted sparsification $x'$ is close to $x^{*0}$ (Step 1 of Proposition EC.3) and, through Lemma EC.2, that $b'=Ax'$ is close to $b$.
--
--   **Formalization Note** The vectors are measurable maps from a probability space into `EuclideanSpace ℝ (Fin d)`; independence is `iIndepFun` and identical distribution is pairwise `IdentDistrib`. The bound $\|w_k\|_2\le C$ holds at every sample point, so $\bar w$ is integrable and $\mathbb E[\bar w]$ is its Bochner integral. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: i.i.d. random vectors with ‖w_k‖₂ ≤ C → measurable maps on a probability space into EuclideanSpace ℝ (Fin d), iIndepFun plus pairwise IdentDistrib, bound at every sample point; reason: the standard measure-theoretic reading of the same hypotheses
--   - reading: K, the number of vectors → 1 ≤ K; reason: the bound contains 1/√K and averages K vectors
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, Lemma EC.1, p.ec7 (attributed to Rahimi and Recht 2009, Lemma 4)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ColumnRandLP

/-- **Lemma EC.1** (Akchen–Mišić, arXiv:2007.10461v5, Lemma EC.1, p.ec7; attributed there to
Rahimi and Recht 2009, Lemma 4). Let `w₁, …, w_K` be i.i.d. random vectors in `ℝ^d` with
`‖w_k‖₂ ≤ C` for every `k`, and `w̄ = (1/K) ∑_k w_k`. For every `δ ∈ (0,1)`, with probability at
least `1 − δ`,
`‖w̄ − E[w̄]‖₂ ≤ C/√K · (1 + √(2 log(1/δ)))`.

**Formalization Note** The vectors live in `EuclideanSpace ℝ (Fin d)` (its norm is `‖·‖₂`) and
are measurable functions on a probability space `(Ω, μ)`; "i.i.d." is `iIndepFun` together with
pairwise `IdentDistrib`. The bound `‖w_k‖₂ ≤ C` holds at every sample point. `E[w̄]` is the
Bochner integral of `w̄`, which is integrable because it is bounded and measurable. `K ≥ 1` (the
paper's `K` is a number of vectors and appears as `1/√K`); `log` is the natural logarithm. -/
theorem lemma_EC_1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d K : ℕ} (hK : 1 ≤ K) (w : Fin K → Ω → EuclideanSpace ℝ (Fin d))
    (hmeas : ∀ k, Measurable (w k)) (hind : iIndepFun w μ)
    (hident : ∀ k k', IdentDistrib (w k) (w k') μ μ)
    (C : ℝ) (hbound : ∀ k ω, ‖w k ω‖ ≤ C) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      μ {ω | ‖(1 / (K : ℝ)) • ∑ k, w k ω - ∫ ω', (1 / (K : ℝ)) • ∑ k, w k ω' ∂μ‖ ≤
        C / Real.sqrt K * (1 + Real.sqrt (2 * Real.log (1 / δ)))} := by sorry

end ColumnRandLP
