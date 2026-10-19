-- Prove2me | Theorems.Thm_ConfoundRobust_Minimax_corollary_4
-- name    : ConfoundRobust.Minimax.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:54.374972+00:00
-- url     : https://prove2.me/theorems/a3974db2-bd0c-4ac8-ab27-8080b70e384f
-- title:
--   Corollary 4, p. 15 — the decomposition of Proposition 3 with the union of monotone weight classes over Π
-- statement:
--   Under the hypotheses of Proposition 3, let $\Pi$ be a class of policies and put $\bar{\mathcal W}^\Gamma = \bigcup_{\pi \in \Pi} \bar{\mathcal W}^\Gamma(\pi)$ and $\bar{\mathcal W}^\Gamma_n = \bigcup_{\pi \in \Pi} \bar{\mathcal W}^\Gamma_n(\pi)$. Then for every $\pi \in \Pi$, every sample size $n$ and every sample,
--   $$\bar R_{\pi_0}(\pi; \mathcal W^\Gamma) = \sum_{t=0}^{m-1} \sup_{W \in \bar{\mathcal W}^\Gamma} R^{(t)}_{\pi_0}(\pi; W), \qquad \hat{\bar R}_{\pi_0}(\pi; \mathcal W^\Gamma_n) = \sum_{t=0}^{m-1} \sup_{W \in \bar{\mathcal W}^\Gamma_n} \hat R^{(t)}_{\pi_0}(\pi; W).$$
--
--   The point is that one weight class, not depending on the policy being evaluated, suffices for all $\pi \in \Pi$ simultaneously; uniform control over $\Pi$ then reduces to uniform control over $\Pi \times \bar{\mathcal W}^\Gamma$.
--
--   **Formalization Note** Policies in $\Pi$ are measurable (as in the definition of a policy). The sample sets are unions of restrictions to the data, as on the page.
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, Corollary 4, p. 15

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

namespace ConfoundRobust.Minimax

theorem corollary_4 {𝒳 : Type} [MeasurableSpace 𝒳] (m : ℕ) (hm : 2 ≤ m)
    (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
    (e : Fin m → 𝒳 → ℝ) (he : IsNominalPropensity μ e) (ν : ℝ) (hν : 0 < ν)
    (heν : ∀ t x, ν ≤ e t x) (he1 : ∀ t x, e t x ≤ 1)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ᵐ z ∂μ, |z.2.2| ≤ B)
    (Γ : ℝ) (hΓ : 1 ≤ Γ)
    (Pol : Set (𝒳 → Fin m → ℝ)) (hPol : ∀ π ∈ Pol, IsPolicy π)
    (π0 : 𝒳 → Fin m → ℝ) (hπ0 : IsPolicy π0)
    (π : 𝒳 → Fin m → ℝ) (hπPol : π ∈ Pol) :
    worstRegret μ π π0 (WSet Γ e) =
        ∑ t, sSup ((fun W => regretT μ π π0 W t) '' (⋃ π' ∈ Pol, WbarSet Γ e π' π0)) ∧
      ∀ (n : ℕ) (ω : Fin n → Obs 𝒳 m),
        sWorstRegret ω π π0 (WSetN Γ e ω) =
          ∑ t, sSup ((fun w => sRegretT ω π π0 w t) '' (⋃ π' ∈ Pol, WbarSetN Γ e π' π0 ω)) := by sorry

end ConfoundRobust.Minimax
