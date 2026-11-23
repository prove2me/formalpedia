-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_radialMap
-- name    : DedekindZeta.ConeRadialReduction.mixedGaussian_radialMap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:16.409296+00:00
-- url     : https://prove2.me/theorems/d7b473a9-cd4e-4c95-8fea-57b60b6d739e
-- title:
--   Cone Radial Reduction: mixed Gaussian radial Map
-- statement:
--   **Radial scaling identity for the Minkowski Gaussian.** With
--   `d = Module.finrank ℚ K`, scaling `σ` radially by `r ≥ 0` along the cone ray
--   (`radialMap K r σ = r^{1/d} • σ`) turns the multiplicative Gaussian into its
--   `r^{2/d}`-power: the Minkowski quadratic form `Q(x) = ∑_w mult w · normAtPlace w x ^ 2`
--   scales as `Q((r^{1/d}•σ)·y) = r^{2/d} · Q(σ·y)` (via `normAtPlace_smul` and
--   `r^{1/d} ≥ 0`), so `mixedGaussian = exp(-π Q)` gives the displayed power law
--   (`Real.exp_mul`). Used to reduce the cone theta integral to a one-dimensional
--   radial Mellin (the standard treatment).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2130-L2156
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2130-L2156

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

theorem DedekindZeta.ConeRadialReduction.mixedGaussian_radialMap (r : ℝ) (hr : 0 ≤ r) (σ y : mixedSpace K) :
    Theta.mixedGaussian K (radialMap K r σ * y)
      = (Theta.mixedGaussian K (σ * y)) ^ (r ^ (2 / (finrank ℚ K : ℝ))) := by sorry
