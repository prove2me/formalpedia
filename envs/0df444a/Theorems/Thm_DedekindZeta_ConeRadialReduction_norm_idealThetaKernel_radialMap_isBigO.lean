-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_idealThetaKernel_radialMap_isBigO
-- name    : DedekindZeta.ConeRadialReduction.norm_idealThetaKernel_radialMap_isBigO
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:00.317946+00:00
-- url     : https://prove2.me/theorems/ccd707a3-28a3-4a36-b5bc-5c5df790f19a
-- title:
--   Cone Radial Reduction: norm ideal Theta Kernel radial Map is Big O
-- statement:
--   **Uniform Gaussian bound on the orbit kernel over the norm-1 surface** (the
--   analytic crux of `orbitTheta_isBigO_exp`). There are `c, α > 0` and `B ≥ 0` such
--   that for every radius `r ≥ 1` and every point `σ` of the norm-1 surface
--   fundamental domain,
--   `‖idealThetaKernel K 𝔞 (radialMap K r σ)‖ ≤ B · exp(-c r^α)`.
--
--   This is the radial blow-up estimate: `radialMap K r σ = r^{1/d} • σ` scales the
--   Minkowski quadratic exponent of every Gaussian summand by `r^{2/d}`, so the
--   whole kernel decays like `exp(-c r^{2/d})` (`α = 2/[K:ℚ]`), uniformly in `σ`
--   over the relatively compact surface. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1495-L1580
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1495-L1580

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

theorem DedekindZeta.ConeRadialReduction.norm_idealThetaKernel_radialMap_isBigO (𝔞 : Ideal (𝓞 K)) :
    ∃ c α B : ℝ, 0 < c ∧ 0 < α ∧ 0 ≤ B ∧
      ∀ r : ℝ, 1 ≤ r → ∀ σ ∈ normEqOneSurface K,
        ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖ ≤ B * Real.exp (-c * r ^ α) := by sorry
