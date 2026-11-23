-- Prove2me | Theorems.Thm_DedekindZeta_map_inv_volume_real_one
-- name    : DedekindZeta.map_inv_volume_real_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:46:59.625658+00:00
-- url     : https://prove2.me/theorems/87a99604-e291-4825-917c-639ea65faa3b
-- title:
--   Dedekind Zeta: map inv volume real one
-- statement:
--   **One-dimensional real inversion Jacobian.** The push-forward of the additive
--   Lebesgue measure on `ℝ` under the field inversion `t ↦ t⁻¹` (with `0⁻¹ = 0`) has
--   density `|t|⁻²` (the absolute value of the Jacobian determinant of `t ↦ t⁻¹`,
--   whose derivative is `-t⁻²`):
--
--       map (·⁻¹) (volume : Measure ℝ) = volume.withDensity (t ↦ |t|⁻²).
--
--   The fixed point `0` is volume-null, so on `ℝ \ {0}` this is the diffeomorphism
--   change of variables `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`.
--   This is the analytic core of the real-factor inversion Jacobian.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L818-L890
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L818-L890

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.map_inv_volume_real_one :
    Measure.map (fun t : ℝ => t⁻¹) volume
      = volume.withDensity (fun t : ℝ => ENNReal.ofReal (‖t‖ ^ 2)⁻¹) := by sorry
