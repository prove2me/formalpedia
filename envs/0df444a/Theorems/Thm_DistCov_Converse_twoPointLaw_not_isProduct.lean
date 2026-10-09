-- Prove2me | Theorems.Thm_DistCov_Converse_twoPointLaw_not_isProduct
-- name    : DistCov.Converse.twoPointLaw_not_isProduct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:30.289761+00:00
-- url     : https://prove2.me/theorems/ce567468-32f7-4918-865d-004b0828a132
-- title:
--   Proof of Proposition 3.15, p. 17, last line — θ := (τ₁ × δ(y₁) + τ₂ × δ(y₂))/2 is not a product measure
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be separable metric spaces. Let $\mu_1\neq\mu_2$ be Borel probability measures on $\mathcal X$ with finite first moments and $D(\mu_1-\mu_2)\ge 0$, let $x_1\neq x_2$ in $\mathcal X$, let $\gamma\in(0,1]$, and put $\tau_i:=\gamma\mu_i+(1-\gamma)\delta(x_i)$. Let $y_1\neq y_2$ in $\mathcal Y$. Then
--   $$\theta:=\tfrac12\big(\tau_1\times\delta(y_1)+\tau_2\times\delta(y_2)\big)$$
--   is not a product measure: $\theta\neq\mu\times\nu$, where $\mu$ and $\nu$ are the marginals of $\theta$.
--
--   This is the closing assertion "yet $\theta$ is not a product measure" of the proof of Proposition 3.15. It holds for every $\gamma\in(0,1]$, in particular for the one with $D(\tau_1-\tau_2)=0$.
--
--   **Formalization Note.** Separability is the standing assumption of Errata (i). The hypotheses $\mu_1\neq\mu_2$ and $D(\mu_1-\mu_2)\ge0$ are those the proof fixes in its second sentence; they guarantee $\tau_1\neq\tau_2$, which the page uses without comment.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 17, proof of Proposition 3.15, last line

import Mathlib
import Definitions.Def_DistCov_Converse_Setting

open MeasureTheory

namespace DistCov.Converse

theorem twoPointLaw_not_isProduct
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : DistCov.Indep.FiniteFirstMoment μ₁) (hμ₂ : DistCov.Indep.FiniteFirstMoment μ₂)
    (hne : μ₁ ≠ μ₂) (hD : 0 ≤ DistCov.Indep.Ddiff μ₁ μ₂) (x₁ x₂ : X) (hx : x₁ ≠ x₂)
    (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) 1) (y₁ y₂ : Y) (hy : y₁ ≠ y₂) :
    ¬ DistCov.Indep.IsProduct (twoPointLaw (mixDirac γ μ₁ x₁) (mixDirac γ μ₂ x₂) y₁ y₂) := by sorry

end DistCov.Converse
