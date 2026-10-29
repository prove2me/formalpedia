-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
-- name    : AvramDividend.Classical.vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:21:00.122998+00:00
-- url     : https://prove2.me/theorems/9e3c3fa3-2e99-4362-846d-5b6e1503add2
-- title:
--   Positive finite barrier candidate is differentiable under Gaussian or regular BV hypotheses
-- statement:
--   Under the classical Standing conditions, q>0 and an IsScaleFunction W, suppose the optimal barrier cstar W is finite and strictly positive. If the Lévy process has a positive Gaussian coefficient or bounded variation, then its barrier value vcstar W is differentiable at the barrier. Gaussian smoothing gives the required C1 scale-function regularity in the first case. In the BV case Standing and BoundedVariation force absolute continuity of the Lévy measure by Condition33, which supplies the C1 positive-scale regularity; positivity of the barrier normalising scale derivative must also be established. This theorem isolates the actual stochastic scale-regularity obligation needed by the smooth-fit target; its deterministic derivative-one consequence is proved separately.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation) :
    DifferentiableAt ℝ (vcstar W) (cstar W).toReal := by sorry
