-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedMulHaar_norm_eq_eq_zero
-- name    : DedekindZeta.ConeRadialReduction.mixedMulHaar_norm_eq_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:49:56.332817+00:00
-- url     : https://prove2.me/theorems/73ae722b-9ae2-4af5-96cb-1d2d855c19fd
-- title:
--   Cone Radial Reduction: mixed Mul Haar norm eq eq zero
-- statement:
--   **Positive norm-level sets are `mixedMulHaar`-null.** For every `c > 0` the
--   fiber `{x | N x = c}` has `mixedMulHaar K`-measure zero. Proof (the standard treatment, radial scaling): `mixedMulHaar` is a `σ`-finite measure
--   (`volume.withDensity` of an everywhere-finite density), so by
--   `countable_meas_level_set_pos` only countably many levels `c` can have
--   `μ {N = c} > 0`. But the radial scaling `radialMap K (a/b)` (measure-preserving,
--   `lintegral_radialMap_mixedMulHaar`) maps `{N = b}` onto `{N = a}`, hence
--   `μ {N = a} = μ {N = b}` for all `a, b > 0`; if one positive level had positive
--   measure then *every* positive level would, contradicting countability (the
--   interval `Ioo 0 1` of levels is uncountable).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2528-L2592
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2528-L2592

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

theorem DedekindZeta.ConeRadialReduction.mixedMulHaar_norm_eq_eq_zero {c : ℝ} (hc : 0 < c) :
    DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = c} = 0 := by sorry
