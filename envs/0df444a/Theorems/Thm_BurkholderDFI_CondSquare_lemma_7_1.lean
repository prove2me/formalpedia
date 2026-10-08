-- Prove2me | Theorems.Thm_BurkholderDFI_CondSquare_lemma_7_1
-- name    : BurkholderDFI.CondSquare.lemma_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:39.640757+00:00
-- url     : https://prove2.me/theorems/0b0b29de-705d-45f3-8642-c1dc41bd242d
-- title:
--   Lemma 7.1 — a good-λ inequality P(g > βλ, f ≤ δλ) ≤ εP(g > λ) gives EΦ(g) ≤ γη/(1 − γε)·EΦ(f)
-- statement:
--   Let $\Phi$ satisfy the conditions of Section 7 (nondecreasing, continuous on $[0,\infty]$, $\Phi(0)=0$, $\Phi(2\lambda)\le c\Phi(\lambda)$). Let $f,g$ be nonnegative measurable functions on a probability space $(\Omega,\mathcal A,P)$ and $\beta>1$, $\delta>0$, $\varepsilon>0$ real numbers such that
--   $$
--   P(g>\beta\lambda,\ f\le\delta\lambda)\le\varepsilon\,P(g>\lambda),\qquad\lambda>0 .
--   $$
--   Let $\gamma,\eta\ge0$ satisfy
--   $$
--   \Phi(\beta\lambda)\le\gamma\Phi(\lambda),\qquad\Phi(\delta^{-1}\lambda)\le\eta\Phi(\lambda),\qquad\lambda>0,
--   $$
--   and suppose $\gamma\varepsilon<1$. Then
--   $$
--   E\Phi(g)\le\frac{\gamma\eta}{1-\gamma\varepsilon}\,E\Phi(f).
--   $$
--
--   This lemma converts a distribution function inequality into a $\Phi$-moment inequality; it is the device by which every "good-$\lambda$" inequality of the paper yields an inequality for all $\Phi$ of moderate growth.
--
--   **Formalization Note** $f$ and $g$ take values in $[0,\infty]$ (the paper's functions are nonnegative and measurable; allowing the value $\infty$ is needed to apply the lemma to $f^*$ or $S(f)$). $\gamma,\eta$ are taken nonnegative, which loses nothing: for $\Phi$ not identically zero, (7.2) forces $\gamma,\eta\ge1$, and for $\Phi\equiv0$ the conclusion is trivial. Expectations are lower Lebesgue integrals in $[0,\infty]$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §7, Lemma 7.1, p. 26

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.CondSquare

/-- Lemma 7.1, p. 26: a good-λ inequality `P(g > βλ, f ≤ δλ) ≤ εP(g > λ)`, together with
`Φ(βλ) ≤ γΦ(λ)`, `Φ(δ⁻¹λ) ≤ ηΦ(λ)` and `γε < 1`, gives `EΦ(g) ≤ γη/(1 − γε) · EΦ(f)`. -/
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

end BurkholderDFI.CondSquare
