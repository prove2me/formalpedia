-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scaleDeriv_tendsto_atTop_of_C1
-- name    : AvramDividend.Classical.bv_scaleDeriv_tendsto_atTop_of_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:12:57.197502+00:00
-- url     : https://prove2.me/theorems/12848c03-3a86-4fa1-9851-61e8600c3554
-- title:
--   Bounded-variation q-scale derivative growth from proved Esscher tilt and C1
-- statement:
--   Under Avram standing assumptions and bounded variation, the already Proved bounded-variation tilted-scale theorem gives strict positivity and a positive exponential rate whose normalised scale function is nondecreasing. Given differentiability on the positive axis, the already Proved deterministic exponential-tilt coercivity theorem gives Tendsto (deriv W) atTop atTop. The only premise beyond the BV classical model is exact positive-axis differentiability, which follows analytically from the standing condition (3.3) but remains to be formally closed in the dedicated regularity workstream.
-- source:
--   Avram Palmowski Pistorius (2007), equation (3.3) and Lemma 2(i), bounded-variation renewal scale-function growth.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scaleDeriv_tendsto_atTop_of_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by sorry
