-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_lintegral_radialMap_mixedMulHaar
-- name    : DedekindZeta.ConeRadialReduction.lintegral_radialMap_mixedMulHaar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:38:59.295253+00:00
-- url     : https://prove2.me/theorems/10749949-db57-48d7-b4e2-cc2ffd8ec564
-- title:
--   Cone Radial Reduction: lintegral radial Map mixed Mul Haar
-- statement:
--   **Radial-scaling invariance of the cone Haar measure** `mixedMulHaar K`.
--   For `t > 0` and nonnegative measurable `h`,
--   `∫⁻ h(radialMap K t x) dμ = ∫⁻ h(x) dμ`. The radial scaling
--   `radialMap K t x = s • x` (`s = t^{1/d} > 0`) is right multiplication by the
--   scalar element `c = s • 1`, which has `N(c) = |s|^d ≠ 0`; the multiplicative
--   Haar `mixedMulHaar K` is invariant under such right translations
--   (`DedekindZeta.lintegral_comp_mul_right_mixedMulHaar`). the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L208-L225
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L208-L225

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

theorem DedekindZeta.ConeRadialReduction.lintegral_radialMap_mixedMulHaar (h : mixedSpace K → ℝ≥0∞)
    (hh : Measurable h) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, h (radialMap K t x) ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ x, h x ∂(DedekindZeta.mixedMulHaar K) := by sorry
