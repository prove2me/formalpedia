-- Prove2me | Theorems.Thm_DistCov_Converse_Ddiff_dirac_neg
-- name    : DistCov.Converse.Ddiff_dirac_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:50.417497+00:00
-- url     : https://prove2.me/theorems/cbb48586-82aa-48ba-8413-fe1172ca0a5a
-- title:
--   Proof of Proposition 3.15, p. 17 — if x₁ ≠ x₂ then D(δ(x₁) − δ(x₂)) < 0
-- statement:
--   Let $\mathcal X$ be a separable metric space and $x_1\neq x_2$ points of $\mathcal X$. Then
--   $$D\big(\delta(x_1)-\delta(x_2)\big)<0.$$
--
--   (Its value is $-2\,d(x_1,x_2)$.) This is the negative endpoint of the interpolation in the next step of the proof of Proposition 3.15.
--
--   **Formalization Note.** Separability is the standing assumption of Errata (i); point masses have finite first moments, so the energies are genuine integrals.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 17, proof of Proposition 3.15, second paragraph, first clause

import Mathlib
import Definitions.Def_DistCov_Converse_Setting

open MeasureTheory

namespace DistCov.Converse

theorem Ddiff_dirac_neg
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (x₁ x₂ : X) (hx : x₁ ≠ x₂) :
    DistCov.Indep.Ddiff (Measure.dirac x₁) (Measure.dirac x₂) < 0 := by sorry

end DistCov.Converse
