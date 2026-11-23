-- Prove2me | Theorems.Thm_DedekindZeta_lintegral_enorm_mixedGaussian_mul_norm_cpow_eq
-- name    : DedekindZeta.lintegral_enorm_mixedGaussian_mul_norm_cpow_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:44:53.858461+00:00
-- url     : https://prove2.me/theorems/d4667128-c3c5-499d-a31a-fd304ca750e2
-- title:
--   Dedekind Zeta: lintegral enorm mixed Gaussian mul norm cpow eq
-- statement:
--   **Per-element whole-space `enorm` scale invariance** for the shifted Minkowski
--   Gaussian Mellin integrand (helper 1). For any
--   nonzero `a : K` and `t : ℂ`, translating the Gaussian argument by `σ a` rescales
--   the whole-space `enorm`-`lintegral` of `g(x·σ a)·N(x)^t` by the constant
--   `𝔑(σ a)^{-Re t} = N(σ a)^{-Re t}`:
--
--       ∫⁻ x, ‖g(x·σ a)·N(x)^t‖ₑ d^*x
--         = ENNReal.ofReal (N(σ a)^{-Re t}) · ∫⁻ x, ‖g(x)·N(x)^t‖ₑ d^*x.
--
--   This is the `lintegral`/`enorm` analogue of
--   `GammaIntegral.mellin_mixedGaussian_mul_eq` (which is downstream and so cannot be
--   cited here): right-translation invariance of `mixedMulHaar`
--   (`mixedMulHaar_map_mul_right`) reduces the integrand to `g(y)·N(y·σ(a)⁻¹)^t`, and
--   `|N(y·σ(a)⁻¹)| = |N y|·|N(σ a)|⁻¹` factors out the constant
--   `N(σ a)^{-Re t}` from the `enorm`. It is stated for a *general* nonzero `a ∈ K`
--   (not just an integral element), as needed by the fractional-ideal assembly.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1524-L1609
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1524-L1609

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

theorem DedekindZeta.lintegral_enorm_mixedGaussian_mul_norm_cpow_eq
    {a : K} (ha : a ≠ 0) (t : ℂ) :
    ∫⁻ x, ‖(Theta.mixedGaussian K (x * mixedEmbedding K a) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K)
      = ENNReal.ofReal (mixedEmbedding.norm (mixedEmbedding K a) ^ (-t.re))
          * ∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) := by sorry
