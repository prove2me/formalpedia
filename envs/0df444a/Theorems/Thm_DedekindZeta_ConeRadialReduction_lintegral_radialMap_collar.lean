-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_lintegral_radialMap_collar
-- name    : DedekindZeta.ConeRadialReduction.lintegral_radialMap_collar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:48:29.840668+00:00
-- url     : https://prove2.me/theorems/b7dd2ac4-45cf-4fb2-a4bf-8716c2a39391
-- title:
--   Cone Radial Reduction: lintegral radial Map collar
-- statement:
--   **Step-1 restricted radial change of variable** (the standard treatment).
--   For `t > 0` and nonnegative measurable `h`, scaling the integration variable by
--   `radialMap K t` turns the collar `C = cone ∩ {N ∈ (1, e]}` into the scaled collar
--   `C_t = cone ∩ {N ∈ (t, e·t]}`:
--     `∫⁻ x in C, h (radialMap K t x) dμ = ∫⁻ y in C_t, h y dμ`.
--   Proof: apply the radial-scaling invariance `lintegral_radialMap_mixedMulHaar` to
--   the nonnegative measurable `g = C_t.indicator h`, using that
--   `radialMap K t x ∈ C_t ↔ x ∈ C` (norm scales by `t` via `norm_radialMap`; the
--   cone is scale-invariant in both directions via `radialMap_mem_cone` and the
--   inverse scaling `radialMap K t⁻¹`). Consumed by the collar disintegration
--   assembly.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L317-L365
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L317-L365

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

theorem DedekindZeta.ConeRadialReduction.lintegral_radialMap_collar (h : mixedSpace K → ℝ≥0∞) (hh : Measurable h)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        h (radialMap K t x) ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ y in (mixedEmbedding.fundamentalCone K ∩
            {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)}),
          h y ∂(DedekindZeta.mixedMulHaar K) := by sorry
