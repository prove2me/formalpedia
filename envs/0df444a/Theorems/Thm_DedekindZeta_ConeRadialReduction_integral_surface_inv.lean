-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_integral_surface_inv
-- name    : DedekindZeta.ConeRadialReduction.integral_surface_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:50:15.534411+00:00
-- url     : https://prove2.me/theorems/b5331f79-1331-4e2c-86c8-ba5f4e494087
-- title:
--   Cone Radial Reduction: integral surface inv
-- statement:
--   **Inversion invariance of the surface integral (modulo the unit action).**
--   For a *unit-invariant* integrand `f` (`f (u • x) = f x` for all `u : (𝓞 K)ˣ`),
--   the norm-1 involution `σ ↦ σ⁻¹` leaves the surface integral unchanged.
--
--   The unit-invariance hypothesis is essential and cannot be dropped. The
--   fundamental cone `mixedEmbedding.fundamentalCone K` is
--   `logMap ⁻¹' (ZSpan.fundamentalDomain …) \ {N = 0}`, and `ZSpan.fundamentalDomain`
--   is the **half-open** parallelepiped `{∑ cᵢ bᵢ : cᵢ ∈ Set.Ico 0 1}`. On the
--   `N ≠ 0` locus `logMap x⁻¹ = - logMap x`, and negation sends `Ico 0 1` into
--   `Ioc (-1) 0`, so `x ∈ cone` does **not** imply `x⁻¹ ∈ cone`: `normEqOneSurface K`
--   is not setwise invariant under `σ ↦ σ⁻¹`, and `surfaceMeasure K` is not invariant
--   under inversion. (Taking `f = indicator (normEqOneSurface K)` exhibits the
--   failure for arbitrary `f`.) the standard treatment's involution acts on the norm-1 torus
--   **modulo units** — its integrand descends to the idele-class quotient, i.e. is
--   invariant under the `(𝓞 K)ˣ`-action — which is exactly the hypothesis `hf`.
--   the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2934-L2993
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2934-L2993

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

theorem DedekindZeta.ConeRadialReduction.integral_surface_inv (f : mixedSpace K → ℂ)
    (hf : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K), f (u • x) = f x)
    (hf_meas : AEStronglyMeasurable f (surfaceMeasure K))
    (hfinv_meas : AEStronglyMeasurable (fun σ => f σ⁻¹) (surfaceMeasure K))
    (hg_meas : AEStronglyMeasurable (fun x => f (radialProj K x))
      (DedekindZeta.mixedMulHaar K))
    (hg_int : IntegrableOn (fun x => f (radialProj K x))
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
      (DedekindZeta.mixedMulHaar K)) :
    ∫ σ in normEqOneSurface K, f σ⁻¹ ∂(surfaceMeasure K)
      = ∫ σ in normEqOneSurface K, f σ ∂(surfaceMeasure K) := by sorry
