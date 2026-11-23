-- Prove2me | Theorems.Thm_DedekindZeta_tsum_lintegral_enorm_cone_mixedThetaKernel_summand_ne_top
-- name    : DedekindZeta.tsum_lintegral_enorm_cone_mixedThetaKernel_summand_ne_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:46:12.616596+00:00
-- url     : https://prove2.me/theorems/dc674b06-e5b7-45ec-a574-6e651b38136a
-- title:
--   Dedekind Zeta: tsum lintegral enorm cone mixed Theta Kernel summand ne top
-- statement:
--   **Dominating finiteness for the fractional cone theta integrand**
--   (analytic core). For any fractional ideal `I` and
--   `1 < t.re`, the element-wise series (over the nonzero `a ∈ I`) of the cone
--   `lintegral`s of the `enorm` of the single shifted Minkowski Gaussian
--   `g(x·σ a)·N(x)^t` is finite.
--
--   This is the genuine convergence threshold (`Re t > 1`): grouping the `a` into
--   `𝓞ˣ`-orbits, each orbit's cone-lintegrals sum to the whole-space Mellin value
--   `𝔑((a))^{-Re t}·|I(Re t)|`, and `∑` over orbits converges by
--   `summable_absNorm_neg_cpow`. It mirrors the *integral*-ideal estimate
--   `GammaIntegral.tsum_lintegral_enorm_cone_mixedGaussian_ne_top`, but is needed here
--   (upstream of `GammaIntegral`) to feed the `Integrable` statement consumed by the
--   class-rescaling glue `dualIdeal_cone_integral_eq` in this module: the per-element
--   cone-Mellin estimate `GammaIntegral.mellin_mixedGaussian_mul_eq` and the
--   fundamental-cone collapse currently live *downstream* in `GammaIntegral`, which
--   `import`s this file, so they cannot be cited here and the estimate must be
--   re-established (or relocated) at this layer.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2454-L2469
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2454-L2469

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal

theorem DedekindZeta.tsum_lintegral_enorm_cone_mixedThetaKernel_summand_ne_top
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) (ht : 1 < t.re) :
    (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K))
      ≠ ∞ := by sorry
