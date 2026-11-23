-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_coneMellin_idealThetaKernel_eq_radial
-- name    : DedekindZeta.ConeRadialReduction.coneMellin_idealThetaKernel_eq_radial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:48:42.402363+00:00
-- url     : https://prove2.me/theorems/9cb09ea0-fa13-4b99-ad48-64fe21113ac3
-- title:
--   Cone Radial Reduction: cone Mellin ideal Theta Kernel eq radial
-- statement:
--   **Radial reduction of the cone Mellin.** Applying the measure decomposition
--   `mixedMulHaar K = μ_S ⊗ dr/r` (`setIntegral_cone_eq_radial`) and the norm scaling
--   `N (radialMap K r σ) = r` (`norm_radialMap_of_mem`) to factor `N(x)^s = r^s` out
--   of the surface integral, the per-class cone Mellin becomes a one-dimensional
--   radial Mellin of the orbit-integrated theta `F = orbitTheta K 𝔞`:
--
--       ∫_cone Θ(𝔞,x)·N(x)^s d^*x = ∫_0^∞ F(𝔞,r)·r^s · r⁻¹ dr .
--
--   Faithful to the standard treatment; no special-case narrowing.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L884-L905
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L884-L905

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

theorem DedekindZeta.ConeRadialReduction.coneMellin_idealThetaKernel_eq_radial (𝔞 : Ideal (𝓞 K)) (s : ℂ)
    (hh : IntegrableOn
        (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s)
        (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K)) :
    ∫ x in mixedEmbedding.fundamentalCone K,
        Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s
          ∂(DedekindZeta.mixedMulHaar K)
      = ∫ r in Set.Ioi (0 : ℝ),
          orbitTheta K 𝔞 r * (r : ℂ) ^ s * (r : ℝ)⁻¹ ∂volume := by sorry
