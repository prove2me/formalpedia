-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_bound_tsum_mixedGaussian_surface
-- name    : DedekindZeta.ConeRadialReduction.exists_bound_tsum_mixedGaussian_surface
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:48:59.055769+00:00
-- url     : https://prove2.me/theorems/2b5948d4-11dd-4aa9-b208-cf0d10b54d5c
-- title:
--   Cone Radial Reduction: exists bound tsum mixed Gaussian surface
-- statement:
--   **Uniform bound on the `r = 1` lattice Gaussian sum over the surface.**
--   There is `M ≥ 0` with `∑'_{a≠0} mixedGaussian K (σ · σ(a)) ≤ M` for every `σ` on
--   the norm-1 surface fundamental domain: the residual convergent lattice theta sum
--   at radius `1`, bounded uniformly over the relatively compact surface. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1430-L1483
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1430-L1483

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

theorem DedekindZeta.ConeRadialReduction.exists_bound_tsum_mixedGaussian_surface (𝔞 : Ideal (𝓞 K)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ normEqOneSurface K,
      ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
        Theta.mixedGaussian K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) ≤ M := by sorry
