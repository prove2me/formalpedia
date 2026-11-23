-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum
-- name    : DedekindZeta.GammaIntegral.completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:47:51.42636+00:00
-- url     : https://prove2.me/theorems/47281f67-77b0-4916-86c2-d2ed41e9156f
-- title:
--   Gamma Integral: completed Partial Zeta eq norm Pow mul ZInfty mul tsum
-- statement:
--   **Step 3 intermediate identity** (the standard analytic argument).  For `1 < Re s`
--   and nonzero `a`, the completed partial zeta is `N(a)^s * Z_inf(s)` times the
--   partial zeta over nonzero principal ideals divisible by `a`.  The analytic core
--   is `cone_integral_idealThetaKernel_eq`; the remaining `(1/w_K)` and
--   `|d_K|^{s/2}*I = Z_inf` bookkeeping (`absdisc_rpow_mul_I_eq_ZInfty`) is algebra.
--   Consumed by step 5.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L2165-L2178
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L2165-L2178

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

theorem DedekindZeta.GammaIntegral.completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    DedekindZeta.completedPartialZeta K a s
      = (Ideal.absNorm a : ℂ) ^ s * DedekindZeta.ZInfty K s *
          ∑' I : {I : (Ideal (RingOfIntegers K))⁰ //
                    (a ∣ (I : Ideal (RingOfIntegers K))) ∧
                      Submodule.IsPrincipal (I : Ideal (RingOfIntegers K))},
              (Ideal.absNorm (I : Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by sorry
