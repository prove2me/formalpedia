-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_C1_of_scale_C1_tilt
-- name    : AvramDividend.Classical.vcstar_C1_of_scale_C1_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:29:17.551549+00:00
-- url     : https://prove2.me/theorems/3e156a18-80cd-4afa-b0c1-e376160ab5d6
-- title:
--   Barrier candidate globally C1 under positive tilted C1 scale assumptions
-- statement:
--   This deterministic-to-stochastic bridge upgrades the positive-barrier candidate to global C1 regularity on positive reserves. The canonical scale is strictly positive under Standing. C1 scale smoothness gives differentiability, while positive monotonicity of an exponential tilt forces the scale derivative at the positive barrier to be strictly positive. An already-Proved gradient result supplies differentiability of the piecewise candidate on the whole positive axis. The focused derivative-pasting helper supplies continuity of its ordinary derivative at the join, and the already-Proved calculus criterion yields ContDiffOn of order one. No general C2 regularity is assumed and the stochastic scale regularity remains an explicit hypothesis.
-- source:
--   Deterministic C1 derivative-pasting and scale-gradient facts with exact stochastic assumptions retained.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_continuous_C1_positive
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_differentiable_continuous_deriv_Ioi
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- Global C1 candidate smoothness from positive tilted C1 scale regularity. -/
theorem vcstar_C1_of_scale_C1_tilt
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcpos : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) := by sorry
end AvramDividend.Classical
