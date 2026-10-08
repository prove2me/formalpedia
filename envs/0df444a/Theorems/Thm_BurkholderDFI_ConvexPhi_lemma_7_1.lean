-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_lemma_7_1
-- name    : BurkholderDFI.ConvexPhi.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:06.182698+00:00
-- url     : https://prove2.me/theorems/ae690236-bba3-48af-bfe7-289ce9347610
-- title:
--   Lemma 7.1 — good-λ principle for Φ inequalities
-- statement:
--   Let $f,g$ be nonnegative measurable random variables. Suppose $\beta>1$, $\delta,\varepsilon>0$ and, for every $\lambda>0$,
--   $$
--   P(g>\beta\lambda,\ f\le\delta\lambda)\le\varepsilon P(g>\lambda).
--   $$
--   If $\Phi$ has moderate growth, $\Phi(\beta\lambda)\le\gamma\Phi(\lambda)$ and $\Phi(\delta^{-1}\lambda)\le\eta\Phi(\lambda)$ for all $\lambda>0$, and $\gamma\varepsilon<1$, then
--   $$
--   E\Phi(g)\le\frac{\gamma\eta}{1-\gamma\varepsilon}E\Phi(f).
--   $$
--   This turns distribution-function estimates into expectation estimates.
--
--   **Formalization Note** The variables and expectations may be infinite. The case $\Phi\equiv0$ is included.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 7.1, p. 26

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Lemma 7.1, p. 26: the good-λ lemma. -/
theorem lemma_7_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (β δ ε : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hε : 0 < ε)
    (h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < g ω})
    (γ η : ℝ≥0)
    (h72 : ∀ l : ℝ, 0 < l →
      Φ (ENNReal.ofReal (β * l)) ≤ γ * Φ (ENNReal.ofReal l) ∧
      Φ (ENNReal.ofReal (δ⁻¹ * l)) ≤ η * Φ (ENNReal.ofReal l))
    (hγε : (γ : ℝ) * ε < 1) :
    ∫⁻ ω, Φ (g ω) ∂P ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * ∫⁻ ω, Φ (f ω) ∂P := by sorry
end BurkholderDFI.ConvexPhi
