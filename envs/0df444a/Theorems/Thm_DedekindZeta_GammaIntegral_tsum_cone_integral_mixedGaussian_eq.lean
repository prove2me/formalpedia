-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_tsum_cone_integral_mixedGaussian_eq
-- name    : DedekindZeta.GammaIntegral.tsum_cone_integral_mixedGaussian_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:47:49.512243+00:00
-- url     : https://prove2.me/theorems/ca308b10-ee65-4d0b-9153-b2cb92326fbb
-- title:
--   Gamma Integral: tsum cone integral mixed Gaussian eq
-- statement:
--   **Step 3 / fundamental-cone collapse + multiplicity count** (the standard analytic argument
--   4/).  The element-wise sum (over nonzero `a' ∈ a`) of the cone integrals of
--   `g(x·σ a') · |N x|^s` collapses to `w_K · I(s)` times the partial zeta over the
--   nonzero principal ideals divisible by `a`.
--
--   Route: the fundamental cone is an `IsFundamentalDomain` for the free unit
--   complement (`isFundamentalDomain_fundamentalCone`); grouping the `a'` into
--   `𝓞ˣ`-orbits, each orbit's cone-terms sum (via `measurePreserving_unitSMul`,
--   `idealThetaKernel_mul_norm_cpow_unitSMul`) to the whole-space integral
--   `∫_{K_ℝ^*} g(x·σ a')·|N x|^s d*x = 𝔑((a'))^{-s} · I(s)`
--   (`mellin_mixedGaussian_mul_eq`), and each nonzero principal ideal divisible by
--   `a` is hit exactly `w_K = torsionOrder K` times
--   (`fundamentalCone.idealSetEquivNorm` / `card_isPrincipal_norm_eq_mul_torsion`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L2013-L2136
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L2013-L2136

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
set_option maxHeartbeats 1600000
variable {K}

theorem DedekindZeta.GammaIntegral.tsum_cone_integral_mixedGaussian_eq (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    ∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
          ∫ x, (mixedEmbedding.fundamentalCone K).indicator
              (fun x => (mixedGaussian K
                  (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
                * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K)
      = (Units.torsionOrder K : ℂ) * I K s *
          ∑' I : {I : (Ideal (RingOfIntegers K))⁰ //
                    (a ∣ (I : Ideal (RingOfIntegers K))) ∧
                      Submodule.IsPrincipal (I : Ideal (RingOfIntegers K))},
              (Ideal.absNorm (I : Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by sorry
