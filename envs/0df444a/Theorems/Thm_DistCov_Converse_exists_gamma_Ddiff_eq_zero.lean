-- Prove2me | Theorems.Thm_DistCov_Converse_exists_gamma_Ddiff_eq_zero
-- name    : DistCov.Converse.exists_gamma_Ddiff_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:24.199027+00:00
-- url     : https://prove2.me/theorems/ef959458-ba21-4ba6-96ca-b9da485f83e6
-- title:
--   Proof of Proposition 3.15, p. 17 — some γ ∈ (0, 1] gives D(τ₁ − τ₂) = 0 for τᵢ := γµᵢ + (1 − γ)δ(xᵢ)
-- statement:
--   Let $\mathcal X$ be a separable metric space, let $\mu_1,\mu_2$ be Borel probability measures on $\mathcal X$ with finite first moments and $D(\mu_1-\mu_2)\ge 0$, and let $x_1\neq x_2$ be points of $\mathcal X$. For $\gamma\in[0,1]$ put $\tau_i:=\gamma\mu_i+(1-\gamma)\delta(x_i)$, $i=1,2$. Then there is $\gamma\in(0,1]$ such that
--   $$D(\tau_1-\tau_2)=0.$$
--
--   This is the step that produces, on a space of negative type which is not of strong negative type (and also off negative type), a pair of probability measures whose energy difference vanishes, to be fed into the two-point law of the proof of Proposition 3.15.
--
--   **Formalization Note.** Separability is the standing assumption of Errata (i). The weights $\gamma$, $1-\gamma$ multiply measures as extended nonnegative reals; this is faithful because $\gamma\in(0,1]$.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 17, proof of Proposition 3.15, second paragraph

import Mathlib
import Definitions.Def_DistCov_Converse_Setting

open MeasureTheory

namespace DistCov.Converse

theorem exists_gamma_Ddiff_eq_zero
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : DistCov.Indep.FiniteFirstMoment μ₁) (hμ₂ : DistCov.Indep.FiniteFirstMoment μ₂)
    (hD : 0 ≤ DistCov.Indep.Ddiff μ₁ μ₂) (x₁ x₂ : X) (hx : x₁ ≠ x₂) :
    ∃ γ ∈ Set.Ioc (0 : ℝ) 1, DistCov.Indep.Ddiff (mixDirac γ μ₁ x₁) (mixDirac γ μ₂ x₂) = 0 := by sorry

end DistCov.Converse
