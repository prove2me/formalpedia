-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_setLIntegral_cone_eq_collar_radial
-- name    : DedekindZeta.ConeRadialReduction.setLIntegral_cone_eq_collar_radial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:48:18.368153+00:00
-- url     : https://prove2.me/theorems/7c5d8f5c-91ca-4c4e-86c6-705e43a1116f
-- title:
--   Cone Radial Reduction: set LIntegral cone eq collar radial
-- statement:
--   **Multiplicative-Haar radial disintegration of the cone Haar measure**
--   (collar form). The cone integral against `mixedMulHaar K` equals the integral,
--   over the norm-collar `C = {x ∈ cone | N x ∈ (1, e]}`, of the radial collapse
--   `∫_0^∞ h(radialMap K t x) · ofReal t⁻¹ dt`.
--
--   This is the genuine mathematical core: `mixedMulHaar K` is multiplicative Haar on
--   the cone (off `N = 0`), invariant under the radial scaling `x ↦ radialMap K t x`
--   (`mixedMulHaar` is a multiplicative Haar measure, cf.
--   `DedekindZeta.lintegral_comp_mul_right_mixedMulHaar`), and the collar `C` is a
--   fundamental domain for that `(0,∞)`-scaling action on the cone with the
--   multiplicative weight `dr/r` (`∫_1^e dr/r = 1`). The norm-vanishing locus is
--   `mixedMulHaar`-null (`DedekindZeta.ae_norm_ne_zero` style), so it does not
--   contribute. the standard treatment; the polar/`expMapBasis` Jacobian underlying
--   Mathlib's `NormLeOne.volume_normLeOne`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L381-L545
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L381-L545

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

theorem DedekindZeta.ConeRadialReduction.setLIntegral_cone_eq_collar_radial (h : mixedSpace K → ℝ≥0∞)
    (hh : Measurable h) :
    ∫⁻ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
            {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          (∫⁻ t in Set.Ioi (0 : ℝ),
              h (radialMap K t x) * ENNReal.ofReal t⁻¹ ∂volume)
            ∂(DedekindZeta.mixedMulHaar K) := by sorry
