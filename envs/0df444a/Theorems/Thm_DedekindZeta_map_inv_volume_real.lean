-- Prove2me | Theorems.Thm_DedekindZeta_map_inv_volume_real
-- name    : DedekindZeta.map_inv_volume_real
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:47:02.621463+00:00
-- url     : https://prove2.me/theorems/3e464f0e-4a07-42a1-82b8-3c6401958f59
-- title:
--   Dedekind Zeta: map inv volume real
-- statement:
--   **Real-factor inversion Jacobian on the mixed space.** Componentwise field
--   inversion `x ↦ (x w)⁻¹` on the real coordinate factor
--   `{w : InfinitePlace K // IsReal w} → ℝ` of `K_ℝ` pushes the additive Lebesgue
--   measure forward to the measure with density `∏_{w real} |x_w|⁻²` — one
--   `|x_w|⁻²` Jacobian factor per real place. Obtained from the one-dimensional
--   input `map_inv_volume_real_one` by the product change of variables
--   (`MeasureTheory.Measure.pi_map_pi` on `volume = Measure.pi (fun _ => volume)`,
--   then the `withDensity` of the product density).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1011-L1038
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1011-L1038

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

theorem DedekindZeta.map_inv_volume_real :
    Measure.map
        (fun x : {w : InfinitePlace K // IsReal w} → ℝ => fun w => (x w)⁻¹)
        volume
      = volume.withDensity
          (fun x : {w : InfinitePlace K // IsReal w} → ℝ =>
            ∏ w, ENNReal.ofReal (‖x w‖ ^ 2)⁻¹) := by sorry
