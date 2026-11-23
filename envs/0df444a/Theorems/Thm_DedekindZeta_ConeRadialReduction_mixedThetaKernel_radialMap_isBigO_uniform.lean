-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedThetaKernel_radialMap_isBigO_uniform
-- name    : DedekindZeta.ConeRadialReduction.mixedThetaKernel_radialMap_isBigO_uniform
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:34.113801+00:00
-- url     : https://prove2.me/theorems/e58fa862-5bb3-495b-83c6-a3fa7e586d4f
-- title:
--   Cone Radial Reduction: mixed Theta Kernel radial Map is Big O uniform
-- statement:
--   **Uniform Gaussian tail of the fractional theta kernel along the radial ray**
--   (the genuine analytic crux). There are `c, α, B > 0` so that for every `r ≥ 1`
--   and every point `σ` of the compact norm-1 surface fundamental domain
--   `normEqOneSurface K`, the radially blown-up kernel obeys
--   `‖Θ_mix(I, radialMap K r σ)‖ ≤ B · e^{-c r^α}`. Since `radialMap K r σ = r^{1/d} • σ`
--   scales each Minkowski coordinate by `r^{1/d}`, the quadratic exponent of every
--   Gaussian summand of `mixedThetaKernel` scales as `r^{2/d}`; bounding the sum by
--   the smallest-nonzero-`I`-lattice-point Gaussian over the compact slice gives a
--   uniform Gaussian bound with `α = 2/[K:ℚ]`. This uniform-in-`σ` bound is what the
--   orbit integral `orbitThetaFrac_isBigO_exp` then integrates over the
--   finite-measure surface. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2169-L2264
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2169-L2264

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

theorem DedekindZeta.ConeRadialReduction.mixedThetaKernel_radialMap_isBigO_uniform (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ c α B : ℝ, 0 < c ∧ 0 < α ∧ 0 ≤ B ∧
      ∀ r : ℝ, 1 ≤ r → ∀ σ ∈ normEqOneSurface K,
        ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖
          ≤ B * Real.exp (-c * r ^ α) := by sorry
