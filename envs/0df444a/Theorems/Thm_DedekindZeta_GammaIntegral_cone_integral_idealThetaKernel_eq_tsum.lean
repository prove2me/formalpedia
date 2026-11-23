-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_cone_integral_idealThetaKernel_eq_tsum
-- name    : DedekindZeta.GammaIntegral.cone_integral_idealThetaKernel_eq_tsum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:47:43.748901+00:00
-- url     : https://prove2.me/theorems/fe8f7230-b2c5-46ad-bd42-bfb51bae9561
-- title:
--   Gamma Integral: cone integral ideal Theta Kernel eq tsum
-- statement:
--   **Step 3 / interchange** (the standard analytic argument).  The cone integral of
--   `idealThetaKernel K a · |N|^s` is the element-wise sum over the nonzero elements
--   of `a` of the cone integrals of the single shifted Minkowski Gaussians
--   `g(x·σ a') · |N x|^s`.  This is the sum/integral interchange step: pull the
--   defining `∑'` of `idealThetaKernel` (Tonelli for the nonnegative Gaussian /
--   dominated convergence for `1 < Re s`, dominating series
--   `summable_absNorm_neg_cpow`) out through the cone integral and the indicator.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1740-L1791
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1740-L1791

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

theorem DedekindZeta.GammaIntegral.cone_integral_idealThetaKernel_eq_tsum (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    ∫ x, (mixedEmbedding.fundamentalCone K).indicator
            (fun x => Theta.idealThetaKernel K a x * (mixedEmbedding.norm x : ℂ) ^ s) x
          ∂(mixedMulHaar K)
      = ∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
          ∫ x, (mixedEmbedding.fundamentalCone K).indicator
              (fun x => (mixedGaussian K
                  (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
                * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K) := by sorry
