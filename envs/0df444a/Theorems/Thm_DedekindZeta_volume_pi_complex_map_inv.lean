-- Prove2me | Theorems.Thm_DedekindZeta_volume_pi_complex_map_inv
-- name    : DedekindZeta.volume_pi_complex_map_inv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:46:55.539049+00:00
-- url     : https://prove2.me/theorems/212de53a-1fb5-4f64-b218-0173a560606e
-- title:
--   Dedekind Zeta: volume pi complex map inv
-- statement:
--   **Complex-factor inversion Jacobian** on the complex coordinate factor of
--   the mixed space. Componentwise inversion `x ↦ (x_w)⁻¹` pushes the additive
--   Lebesgue measure forward to the density `∏_w |x_w|⁻⁴`, the product over complex
--   places of the one-dimensional Jacobian `volume_complex_map_inv`, obtained via
--   `MeasureTheory.Measure.pi_map_pi` / `volume_pi`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L783-L806
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L783-L806

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
open Classical

theorem DedekindZeta.volume_pi_complex_map_inv :
    Measure.map (fun x : {w : InfinitePlace K // IsComplex w} → ℂ => fun w => (x w)⁻¹) volume
      = volume.withDensity
          (fun x : {w : InfinitePlace K // IsComplex w} → ℂ => ∏ w, ENNReal.ofReal (‖x w‖ ^ 4)⁻¹) := by sorry
