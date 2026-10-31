-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_source_crossing_quadratic_strip
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_source_crossing_quadratic_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:13:10.884144+00:00
-- url     : https://prove2.me/theorems/649802cd-f45a-456e-934e-0dc55ef2ca79
-- title:
--   Original Gaussian Lévy generator crossing strip is integrable with quadratic jump-size bound
-- statement:
--   For the unchanged original spectrally negative Lévy source, Standing, q>0, its original q-scale W and σ>0, the absolute compensated generator kernel on the origin-crossing state interval x∈(0,−y) is integrable for each small negative jump −1<y<0, and its total mass is bounded by a source-dependent constant times y². Use the Proved uniform positive-origin envelope on W and W', genuine scale support, the Proved pointwise crossing estimate and exact strip integral bound. Prove strip integrability from Gaussian C2 state continuity, finite strip volume and uniform domination.
-- source:
--   Avram–Palmowski–Pistorius (2007), Gaussian q-scale generator, native compensated Lévy small-jump boundary strip; Proved source 3ff3f1b9 and native e1b2764c/36b53f5a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_scale_origin_linear_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_origin_crossing_compensated_increment_linear_bound
import Theorems.Thm_AvramDividend_Classical_origin_crossing_strip_norm_integral_bound
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_negative_jump_reflection
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_continuousAt_away_shift_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_05_gaussian_source_crossing_quadratic_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, -1 < y → y < 0 →
        IntegrableOn
          (fun x : ℝ => |SpectrallyNegativeLevy.generatorIntegrand W x y|)
          (Ioo (0 : ℝ) (-y)) ∧
        (∫ x in Ioo (0 : ℝ) (-y),
          |SpectrallyNegativeLevy.generatorIntegrand W x y|) ≤
          C * y ^ 2 := by sorry
