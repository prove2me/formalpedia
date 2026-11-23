-- Prove2me | Theorems.Thm_DedekindZeta_ConeMellinBridge_coneMellin_eq_mellinContinuation
-- name    : DedekindZeta.ConeMellinBridge.coneMellin_eq_mellinContinuation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:50:31.587949+00:00
-- url     : https://prove2.me/theorems/00c0bee2-d526-4ae7-b203-4165be5089b9
-- title:
--   Cone Mellin Bridge: cone Mellin eq mellin Continuation
-- statement:
--   **Core bridge.** On `Re s > 1`, the raw cone Mellin integral
--   `∫_cone Θ(𝔞,x)·N(x)^s d^*x` of `completedPartialZeta` equals the **regularised
--   analytic continuation** `mellinContinuation (radialTheta K 𝔞) …` of the reduced
--   radial Mellin, instantiated at the cone-scaling weight `k = 1`, constants
--   `a₀ = b₀ = surfaceVolume K` and inversion constant `C = (covolume K 𝔞)⁻¹`.
--
--   Assembled from the cone→radial reduction
--   (`coneMellin_idealThetaKernel_eq_mellin`), the constant-term restoration
--   (`reducedMellin_radialTheta`), and the Mellin-principle identity on `Re s > k`
--   (`mellinContinuation_eq`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L148-L159
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L148-L159

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Definitions.Def_DedekindZeta_ConeMellinBridge
set_option autoImplicit true
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors
open DedekindZeta DedekindZeta.ConeMellinBridge
open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem DedekindZeta.ConeMellinBridge.coneMellin_eq_mellinContinuation (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) {s : ℂ}
    (hs : 1 < s.re) :
    (∫ x in mixedEmbedding.fundamentalCone K,
        Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s
          ∂(DedekindZeta.mixedMulHaar K))
      = mellinContinuation (radialTheta K 𝔞) (radialThetaDual K 𝔞)
          (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s := by sorry
