-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_radialTheta_inversion
-- name    : DedekindZeta.ConeRadialReduction.radialTheta_inversion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:40:07.579393+00:00
-- url     : https://prove2.me/theorems/f40a2577-e880-484b-b219-5c36a2f1d2fd
-- title:
--   Cone Radial Reduction: radial Theta inversion
-- statement:
--   **Orbit-integrated inversion law** (the orbit-level form of
--   `Theta.idealThetaKernel_inversion`): for `r > 0` and `𝔞 ≠ 0`,
--   `F(𝔞, 1/r) = (1/covol 𝔞) · r · G(𝔞, r)`. Derived by substituting the kernel
--   inversion into the surface integral, using the norm-1 involution `σ ↦ σ⁻¹` and
--   `∫_S 1 = V` to absorb the additive `±1` corrections into the constant `V` of the
--   completed thetas. This is exactly `IsMellinPair.hfe` with `C = (covol 𝔞)⁻¹`,
--   `k = 1`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L3130-L3166
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L3130-L3166

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

theorem DedekindZeta.ConeRadialReduction.radialTheta_inversion (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (r : ℝ) (hr : 0 < r) :
    radialTheta K 𝔞 (1 / r)
      = (Theta.covolume K 𝔞 : ℂ)⁻¹ * ((r ^ (1 : ℝ) : ℝ) : ℂ) * radialThetaDual K 𝔞 r := by sorry
