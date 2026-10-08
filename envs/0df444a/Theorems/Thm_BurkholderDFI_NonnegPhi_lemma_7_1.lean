-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegPhi_lemma_7_1
-- name    : BurkholderDFI.NonnegPhi.lemma_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:31.611315+00:00
-- url     : https://prove2.me/theorems/c6231e28-4d5a-4c10-b2b0-c94065bde293
-- title:
--   Lemma 7.1 — a good-λ inequality P(g > βλ, f ≤ δλ) ≤ εP(g > λ) gives EΦ(g) ≤ γη/(1 − γε)·EΦ(f)
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space and $\Phi:[0,\infty]\to[0,\infty]$ a non-decreasing continuous function with $\Phi(0)=0$ and $\Phi(2\lambda)\le c\Phi(\lambda)$. Let $f,g$ be nonnegative measurable functions on $\Omega$ (possibly taking the value $\infty$), and let $\beta>1$, $\delta>0$, $\varepsilon>0$ be real numbers such that
--   $$P(g>\beta\lambda,\ f\le\delta\lambda)\le\varepsilon\,P(g>\lambda),\qquad\lambda>0.\tag{7.1}$$
--   Let $\gamma,\eta\ge0$ satisfy
--   $$\Phi(\beta\lambda)\le\gamma\Phi(\lambda),\qquad\Phi(\delta^{-1}\lambda)\le\eta\Phi(\lambda),\qquad\lambda>0,\tag{7.2}$$
--   and suppose $\gamma\varepsilon<1$. Then
--   $$E\Phi(g)\le\frac{\gamma\eta}{1-\gamma\varepsilon}\,E\Phi(f).\tag{7.3}$$
--
--   This lemma converts a distribution function (good-$\lambda$) inequality into an inequality between $\Phi$-moments, for every $\Phi$ of moderate growth at once; it is the bridge from Theorem 18.2 to Theorem 18.3.
--
--   **Formalization Note** The paper takes $\gamma,\eta$ real; here they are nonnegative, which loses nothing: if $\Phi$ is not identically zero, (7.2) forces $\gamma,\eta\ge1$, and if $\Phi\equiv0$ the conclusion is trivial. The paper's $f,g$ are nonnegative measurable functions; allowing the value $\infty$ is needed to apply the lemma to $g=S(f)$ and $f=f^*$. The paper excludes $\Phi\equiv0$; here it is allowed.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 7.1, (7.1)–(7.3), p. 26

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegPhi

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

end BurkholderDFI.NonnegPhi
