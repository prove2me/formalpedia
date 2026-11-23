-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_cone_integral_idealThetaKernel_eq
-- name    : DedekindZeta.GammaIntegral.cone_integral_idealThetaKernel_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:48:37.028808+00:00
-- url     : https://prove2.me/theorems/e7c260cc-0389-4e2d-abeb-7d3cdb32e3a4
-- title:
--   Gamma Integral: cone integral ideal Theta Kernel eq
-- statement:
--   **Cone integral of the lattice theta kernel** (the standard analytic argument).
--   For `1 < Re s` and nonzero `a`, the multiplicative-Haar integral of
--   `idealThetaKernel K a * |N|^s` over the fundamental cone equals `w_K * I(s)` times
--   the partial zeta over the nonzero principal ideals divisible by `a`.
--   Assembled from the interchange step (`cone_integral_idealThetaKernel_eq_tsum`)
--   and the fundamental-cone collapse (`tsum_cone_integral_mixedGaussian_eq`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L2145-L2156
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L2145-L2156

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped nonZeroDivisors
variable {K}

theorem DedekindZeta.GammaIntegral.cone_integral_idealThetaKernel_eq (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    ∫ x, (mixedEmbedding.fundamentalCone K).indicator
            (fun x => Theta.idealThetaKernel K a x * (mixedEmbedding.norm x : ℂ) ^ s) x
          ∂(mixedMulHaar K)
      = (Units.torsionOrder K : ℂ) * I K s *
          ∑' I : {I : (Ideal (RingOfIntegers K))⁰ //
                    (a ∣ (I : Ideal (RingOfIntegers K))) ∧
                      Submodule.IsPrincipal (I : Ideal (RingOfIntegers K))},
              (Ideal.absNorm (I : Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by sorry
