-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_tsum_lintegral_enorm_cone_mixedGaussian_ne_top
-- name    : DedekindZeta.GammaIntegral.tsum_lintegral_enorm_cone_mixedGaussian_ne_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:36:39.62707+00:00
-- url     : https://prove2.me/theorems/509a3888-d266-4c4b-9843-3ed3deba7ee0
-- title:
--   Gamma Integral: tsum lintegral enorm cone mixed Gaussian ne top
-- statement:
--   **L¹/Tonelli finiteness** for the interchange step (the standard treatment): the
--   element-wise sum (over nonzero `a' ∈ a`) of the cone `lintegral`s of the `enorm`
--   of `g(x·σ a')·|N x|^s` is finite for `1 < Re s`.  This is the dominated/Tonelli
--   bound underlying the sum/integral interchange: grouping the `a'` into `𝓞ˣ`-orbits,
--   each orbit's cone-lintegrals sum to the whole-space integral
--   `𝔑((a'))^{-Re s}·I(Re s)`, and `∑` over orbits converges by
--   `summable_absNorm_neg_cpow`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1619-L1730
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1619-L1730

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

theorem DedekindZeta.GammaIntegral.tsum_lintegral_enorm_cone_mixedGaussian_ne_top (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    (∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun x => (mixedGaussian K
                (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ ∂(mixedMulHaar K))
      ≠ ∞ := by sorry
