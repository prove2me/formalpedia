-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_setIntegral_collar_shift
-- name    : DedekindZeta.ConeRadialReduction.setIntegral_collar_shift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:50:05.37427+00:00
-- url     : https://prove2.me/theorems/ad057262-7c96-44c7-bd01-8d523f6af224
-- title:
--   Cone Radial Reduction: set Integral collar shift
-- statement:
--   **Bochner collar shift** (`ℂ`-valued analogue of `lintegral_collar_shift`).
--   For a measurable scale-invariant set `S` (membership equivalence
--   `radialMap K t x ∈ S ↔ x ∈ S` for `t > 0`) and a radial-scale-invariant
--   measurable `g : mixedSpace K → ℂ`, the `mixedMulHaar`-integral of `g` over
--   `S ∩ {N ∈ (t, e·t]}` is independent of the collar position `t > 0`. The radial
--   scaling `radialMap K t = (· * c)` (with `N c ≠ 0`) is `mixedMulHaar`-measure-
--   preserving (`mixedMulHaar_map_mul_right`), so the substitution `x ↦ radialMap K t x`
--   on the half-open collar identifies the two integrals. No integrability is needed.
--   the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2605-L2667
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2605-L2667

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

theorem DedekindZeta.ConeRadialReduction.setIntegral_collar_shift {S : Set (mixedSpace K)} (hS : MeasurableSet S)
    (hSinv : ∀ (t : ℝ), 0 < t → ∀ x, (radialMap K t x ∈ S ↔ x ∈ S))
    (g : mixedSpace K → ℂ)
    (hg : AEStronglyMeasurable g (DedekindZeta.mixedMulHaar K))
    (hgscale : ∀ (t : ℝ), 0 < t → ∀ x, g (radialMap K t x) = g x)
    {t : ℝ} (ht : 0 < t) :
    ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc t (Real.exp 1 * t)}),
        g x ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          g x ∂(DedekindZeta.mixedMulHaar K) := by sorry
