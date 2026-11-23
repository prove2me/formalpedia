-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedMulHaar_collar_integral_inv_eq
-- name    : DedekindZeta.ConeRadialReduction.mixedMulHaar_collar_integral_inv_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:50:06.417039+00:00
-- url     : https://prove2.me/theorems/5e00edce-88d4-4c36-b5df-34fa3c7843b7
-- title:
--   Cone Radial Reduction: mixed Mul Haar collar integral inv eq
-- statement:
--   **Collar-reflection crux: inversion preserves the norm-collar Haar integral
--   for scale + unit-invariant integrands.** Let
--   `C = mixedEmbedding.fundamentalCone K ∩ {x | N x ∈ Set.Ioc 1 (Real.exp 1)}` be the
--   norm-collar of the fundamental cone. For an integrand `g` that is *both*
--   unit-invariant (`g (u • x) = g x`) and radial-scale-invariant
--   (`g (radialMap K t x) = g x` for `t > 0`), the group inversion `x ↦ x⁻¹` leaves
--   the `mixedMulHaar K`-integral over `C` unchanged:
--
--       ∫_C g(x⁻¹) dμ_Haar = ∫_C g(x) dμ_Haar.
--
--   This is the geometric core (part (b)) of the norm-1 surface inversion law
--   `integral_surface_inv`, and the only piece of it not already available upstream.
--
--   Math (the standard treatment). `mixedMulHaar K` is inversion-invariant on the
--   punctured mixed space (`DedekindZeta.GammaIntegral.mixedMulHaar_map_inv`), so the
--   measurable involution `y = x⁻¹` gives `∫_C g(x⁻¹) dμ = ∫_{C⁻¹} g dμ`, where
--   `C⁻¹ = inv(cone) ∩ {N ∈ [1/e, 1)}` (using `mixedEmbedding_norm_inv :
--   N x⁻¹ = (N x)⁻¹`). Both `C` and `C⁻¹` are fundamental domains for the same
--   combined `(0,∞)`-scaling × `(𝓞 K)ˣ`-action on the norm-nonzero locus: the cone is
--   a fundamental domain for the unit action
--   (`isFundamentalDomain_fundamentalCone`), and within a scale-invariant set the
--   half-open collar `{N ∈ (1,e]}` is a fundamental domain for the radial scaling
--   with weight `dr/r` (`∫_1^e dr/r = 1`, `lintegral_collar_weight`). Inversion maps
--   cone → inv(cone) commuting with the unit action and reflects the collar; for `g`
--   invariant under both actions the integral over either fundamental domain agrees
--   (cf. the whole-cone analogue
--   `DedekindZeta.GammaIntegral.mixedMulHaar_integral_inv_cone_eq`, which handles the
--   unit-fundamental-domain step; the new content is the radial collar reflection on
--   top of it).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2763-L2915
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2763-L2915

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

theorem DedekindZeta.ConeRadialReduction.mixedMulHaar_collar_integral_inv_eq (g : mixedSpace K → ℂ)
    (hunit : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K), g (u • x) = g x)
    (hscale : ∀ (t : ℝ), 0 < t → ∀ x, g (radialMap K t x) = g x)
    (hmeas : AEStronglyMeasurable g (DedekindZeta.mixedMulHaar K))
    (hint : IntegrableOn g
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
      (DedekindZeta.mixedMulHaar K)) :
    ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        g x⁻¹ ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        g x ∂(DedekindZeta.mixedMulHaar K) := by sorry
