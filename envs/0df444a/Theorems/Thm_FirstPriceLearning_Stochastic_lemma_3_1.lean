-- Prove2me | Theorems.Thm_FirstPriceLearning_Stochastic_lemma_3_1
-- name    : FirstPriceLearning.Stochastic.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:15.787295+00:00
-- url     : https://prove2.me/theorems/9bc76b3f-701b-4c96-9699-3bc0f53b3b77
-- title:
--   Lemma 3.1, p. 19 — iid points of a poset of width β: 𝔼∑_t (1 + #{s<t : X_s ⪯ X_t})⁻¹ ≤ β(1 + log T)²
-- statement:
--   Let $(\mathcal X,\preceq)$ be a finite partially ordered set whose independence number (the largest number of pairwise incomparable elements) is at most $\beta$, and let $X_1,\dots,X_T$ ($T\ge1$) be iid random variables with values in $\mathcal X$. Then
--
--   $$
--   \mathbb E\left[\sum_{t=1}^T\Big(1+\sum_{s<t}\mathbb 1(X_s\preceq X_t)\Big)^{-1}\right]\ \le\ \beta\,(1+\log T)^2 .
--   $$
--
--   In the analysis of Algorithm 3 the $X_t$ are the iid contexts; the bound is where stochastic contexts help, replacing the number of contexts $M$ by the width $\beta$ of the context order.
--
--   **Formalization Note.** The paper says "iid real-valued random variables taking value in a finite partially ordered set"; the variables are taken with values in the finite poset itself, with the discrete σ-algebra, mutually independent (`iIndepFun`) and identically distributed. The independence number enters as an upper bound on antichain sizes, which gives the same theorem because the bound increases with $\beta$. $\log$ is the natural logarithm.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 19, Lemma 3 (part 1)

import Mathlib

namespace FirstPriceLearning.Stochastic

open MeasureTheory ProbabilityTheory

open scoped Classical in
/-- Lemma 3, part 1 (p. 19): let `X_1, …, X_T` be iid random variables with values in a finite
partially ordered set `(𝒳, ⪯)` whose independence number (largest antichain) is at most `β`. Then
`𝔼[∑_{t=1}^T (1 + ∑_{s<t} 𝟙(X_s ⪯ X_t))^{-1}] ≤ β (1 + log T)^2`. -/
theorem lemma_3_1 {Ω 𝒳 : Type*} [MeasurableSpace Ω] [Fintype 𝒳] [PartialOrder 𝒳]
    [MeasurableSpace 𝒳] [DiscreteMeasurableSpace 𝒳] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (hT : 1 ≤ T) (X : Fin T → Ω → 𝒳) (hX : ∀ t, Measurable (X t))
    (hind : iIndepFun X P) (hid : ∀ s t, IdentDistrib (X s) (X t) P P) (β : ℕ)
    (hβ : ∀ S : Finset 𝒳, IsAntichain (· ≤ ·) (S : Set 𝒳) → S.card ≤ β) :
    ∫ ω, ∑ t : Fin T,
        (1 + ((Finset.univ.filter (fun s : Fin T => s < t ∧ X s ω ≤ X t ω)).card : ℝ))⁻¹ ∂P ≤
      β * (1 + Real.log T) ^ 2 := by sorry

end FirstPriceLearning.Stochastic
