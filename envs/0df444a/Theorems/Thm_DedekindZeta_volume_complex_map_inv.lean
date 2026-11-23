-- Prove2me | Theorems.Thm_DedekindZeta_volume_complex_map_inv
-- name    : DedekindZeta.volume_complex_map_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:44.150117+00:00
-- url     : https://prove2.me/theorems/75d3d420-7e99-414a-ae10-7c8eccb89121
-- title:
--   Dedekind Zeta: volume complex map inv
-- statement:
--   **One-dimensional complex inversion Jacobian.** Pushing the additive
--   Lebesgue measure on `ℂ` forward along `z ↦ z⁻¹` gives `|z|⁻⁴ dλ`. The fixed
--   point `0` is volume-null; off it, `z ↦ z⁻¹` is a diffeomorphism whose real
--   Fréchet derivative `-z⁻²·(·)` is `ℂ`-linear with `|det_ℝ| = |z|⁻⁴`
--   (`integral_image_eq_integral_abs_det_fderiv_smul`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L722-L775
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L722-L775

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

theorem DedekindZeta.volume_complex_map_inv :
    Measure.map (fun z : ℂ => z⁻¹) volume
      = volume.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ 4)⁻¹) := by sorry
