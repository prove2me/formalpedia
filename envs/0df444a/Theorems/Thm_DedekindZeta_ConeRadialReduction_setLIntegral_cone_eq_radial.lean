-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_setLIntegral_cone_eq_radial
-- name    : DedekindZeta.ConeRadialReduction.setLIntegral_cone_eq_radial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:48:16.496648+00:00
-- url     : https://prove2.me/theorems/d7985cb1-1b39-4486-a0bb-9206821a956d
-- title:
--   Cone Radial Reduction: set LIntegral cone eq radial
-- statement:
--   **Lebesgue (`ℝ≥0∞`) form of the measure decomposition**, for nonnegative
--   measurable integrands — the unconditional `lintegral` statement that powers the
--   Bochner version and the `IsMellinPair` decay estimates.
--
--   Proof: assemble the collar-form core (`setLIntegral_cone_eq_collar_radial`) with
--   the `surfaceMeasure` pushforward.  Unfolding `surfaceMeasure K = map (radialProj K)
--   (μ.restrict C)` and using `radialMap K r (radialProj K x) = radialMap K (r / N x) x`
--   (`radialMap_radialMap`) rewrites the inner surface integral as a collar integral;
--   Tonelli (`lintegral_lintegral_swap`) swaps the `r`- and `x`-integrals, and the
--   `r = N x · t` substitution (`lintegral_Ioi_const_mul`) collapses each fibre to the
--   collar core's `dt/t` integral.  the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L593-L733
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L593-L733

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

theorem DedekindZeta.ConeRadialReduction.setLIntegral_cone_eq_radial (h : mixedSpace K → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ r in Set.Ioi (0 : ℝ),
          (∫⁻ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K))
            * ENNReal.ofReal (r⁻¹) ∂volume := by sorry
