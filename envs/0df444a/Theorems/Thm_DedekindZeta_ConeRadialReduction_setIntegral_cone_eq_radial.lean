-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_setIntegral_cone_eq_radial
-- name    : DedekindZeta.ConeRadialReduction.setIntegral_cone_eq_radial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:48:35.789855+00:00
-- url     : https://prove2.me/theorems/4a7b8666-8609-46ab-bed9-67e3882e6a7e
-- title:
--   Cone Radial Reduction: set Integral cone eq radial
-- statement:
--   **Measure decomposition of the cone Haar measure** (Bochner, `ℂ`-valued).
--
--   For `h` integrable over the cone against `mixedMulHaar K`, the cone integral
--   factors through the norm-1 surface × radial `(0,∞)` decomposition with the
--   multiplicative-Haar weight `dr/r`:
--
--       ∫_cone h x d^*x
--         = ∫_0^∞ (∫_{S K} h (radialMap K r σ) dμ_S σ) · r⁻¹ dr .
--
--   Reuses `bijOn_radialMap`, the polar/`expMapBasis` Jacobian underlying the
--   `normLeOne` volume computation, and the `dr/r`-collar definition of
--   `surfaceMeasure`. Faithful to the standard treatment; no special-case narrowing.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L803-L851
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L803-L851

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

theorem DedekindZeta.ConeRadialReduction.setIntegral_cone_eq_radial (h : mixedSpace K → ℂ)
    (hh : IntegrableOn h (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K)) :
    ∫ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K)
      = ∫ r in Set.Ioi (0 : ℝ),
          (∫ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K)) * (r : ℝ)⁻¹
            ∂volume := by sorry
