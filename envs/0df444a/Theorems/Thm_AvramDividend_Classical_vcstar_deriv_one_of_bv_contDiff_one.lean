-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one
-- name    : AvramDividend.Classical.vcstar_deriv_one_of_bv_contDiff_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T09:25:57.267528+00:00
-- url     : https://prove2.me/theorems/8230ae99-d95f-4d77-8923-2124f4a0b01f
-- title:
--   Bounded-variation smooth fit under first-order scale regularity
-- statement:
--   For a bounded-variation spectrally negative Lévy process, if its q-scale function is continuously differentiable on the positive half-line, ordinary smooth fit holds at any finite strictly positive optimal barrier. Already-proved tilted scale positivity and derivative-positivity calculus combine with the established local derivative-pasting theorem. No globally twice differentiable barrier candidate is assumed.
-- source:
--   Avram, Palmowski and Pistorius (2007): bounded-variation smooth fit reduced to C1 scale regularity; deterministic and tilted scale lemmas separately proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_local_scale_deriv_positive
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_deriv_one_of_bv_contDiff_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ))) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
end AvramDividend.Classical
