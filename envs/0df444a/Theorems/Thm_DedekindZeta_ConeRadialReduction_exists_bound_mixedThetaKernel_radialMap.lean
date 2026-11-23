-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_bound_mixedThetaKernel_radialMap
-- name    : DedekindZeta.ConeRadialReduction.exists_bound_mixedThetaKernel_radialMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:39:37.79656+00:00
-- url     : https://prove2.me/theorems/22643dfa-a6b5-4bca-9f31-1ab248687bee
-- title:
--   Cone Radial Reduction: exists bound mixed Theta Kernel radial Map
-- statement:
--   **Uniform bound for the mixed theta kernel on the radius-`r` surface slice.**
--   For `r > 0` there is a constant `C` with
--   `‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ≤ C` for every
--   `σ ∈ normEqOneSurface K`.  Obtained by bounding the continuous function
--   (`continuousOn_mixedThetaKernel_radialMap`) over the compact closure
--   (`isCompact_closure_normEqOneSurface`, `IsCompact.exists_bound_of_continuousOn`)
--   and restricting to `normEqOneSurface K ⊆ closure (normEqOneSurface K)`.  This is
--   the form the integrability child consumes via `Integrable.mono'`.
--   the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1636-L1642
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1636-L1642

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)

theorem DedekindZeta.ConeRadialReduction.exists_bound_mixedThetaKernel_radialMap (I : FractionalIdeal (𝓞 K)⁰ K)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, ∀ σ ∈ normEqOneSurface K,
      ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ≤ C := by sorry
