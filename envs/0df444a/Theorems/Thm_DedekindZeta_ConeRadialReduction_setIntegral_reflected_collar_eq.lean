-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_setIntegral_reflected_collar_eq
-- name    : DedekindZeta.ConeRadialReduction.setIntegral_reflected_collar_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:50:07.884621+00:00
-- url     : https://prove2.me/theorems/a2ec158f-7ff5-4441-8a93-b76375518544
-- title:
--   Cone Radial Reduction: set Integral reflected collar eq
-- statement:
--   **Bochner reflected collar** (`ℂ`-valued analogue of
--   `lintegral_reflected_collar_eq`). For a measurable scale-invariant set `S` and a
--   radial-scale-invariant measurable `g`, the integral over the reflected collar
--   `S ∩ {N ∈ [1/e, 1)}` equals the integral over the half-open collar
--   `S ∩ {N ∈ (1, e]}`. Route: `[1/e, 1)` agrees with `(1/e, 1] = (1/e, e·(1/e)]`
--   up to the `mixedMulHaar`-null boundary norm-levels `{N = 1/e}`, `{N = 1}`
--   (`mixedMulHaar_norm_eq_eq_zero`), to which `setIntegral_collar_shift` applies
--   with `t = 1/e`. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2677-L2731
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2677-L2731

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

theorem DedekindZeta.ConeRadialReduction.setIntegral_reflected_collar_eq {S : Set (mixedSpace K)} (hS : MeasurableSet S)
    (hSinv : ∀ (t : ℝ), 0 < t → ∀ x, (radialMap K t x ∈ S ↔ x ∈ S))
    (g : mixedSpace K → ℂ)
    (hg : AEStronglyMeasurable g (DedekindZeta.mixedMulHaar K))
    (hgscale : ∀ (t : ℝ), 0 < t → ∀ x, g (radialMap K t x) = g x) :
    ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ico (Real.exp 1)⁻¹ 1}),
        g x ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          g x ∂(DedekindZeta.mixedMulHaar K) := by sorry
