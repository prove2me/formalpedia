-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_coneMellin_idealThetaKernel_eq_mellin
-- name    : DedekindZeta.ConeRadialReduction.coneMellin_idealThetaKernel_eq_mellin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:48:40.823799+00:00
-- url     : https://prove2.me/theorems/2af6156f-6187-4381-8358-2107e15f6d49
-- title:
--   Cone Radial Reduction: cone Mellin ideal Theta Kernel eq mellin
-- statement:
--   **The per-class cone Mellin is `mellin (F 𝔞)`.** Combining
--   `coneMellin_idealThetaKernel_eq_radial` with `radialIntegral_eq_mellin`: the cone
--   Mellin integral equals the one-dimensional Mellin transform of the
--   orbit-integrated radial theta `F = orbitTheta K 𝔞`. This is the shape consumed
--   by the abstract Mellin principle.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L928-L936
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L928-L936

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

theorem DedekindZeta.ConeRadialReduction.coneMellin_idealThetaKernel_eq_mellin (𝔞 : Ideal (𝓞 K)) (s : ℂ)
    (hh : IntegrableOn
        (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s)
        (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K)) :
    ∫ x in mixedEmbedding.fundamentalCone K,
        Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s
          ∂(DedekindZeta.mixedMulHaar K)
      = mellin (orbitTheta K 𝔞) s := by sorry
