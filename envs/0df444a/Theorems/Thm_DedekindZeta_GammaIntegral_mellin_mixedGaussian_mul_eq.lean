-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_mellin_mixedGaussian_mul_eq
-- name    : DedekindZeta.GammaIntegral.mellin_mixedGaussian_mul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:47:26.22088+00:00
-- url     : https://prove2.me/theorems/42fab43c-96fb-4d96-96b7-0c0c6f3824ff
-- title:
--   Gamma Integral: mellin mixed Gaussian mul eq
-- statement:
--   **Per-element multiplicative-Haar scale invariance** (the standard treatment): for
--   `a ≠ 0`, the multiplicative Mellin transform of the single shifted Minkowski
--   Gaussian `x ↦ g(x·σ(a))` over `K_ℝ^*` collapses to the element-norm power times
--   the archimedean Gamma factor:
--
--       ∫_{K_ℝ^*} g(x·σ(a)) |N(x)|^s d^*x = 𝔑((a))^{-s} · I(s).
--
--   Proof: left-translation invariance of `mixedMulHaar` under `x ↦ x·σ(a)`
--   (`mulHaar_integral_comp_mul_right`) turns the integrand into
--   `g(y)·|N(y·σ(a)⁻¹)|^s`; then `|N(y·σ(a)⁻¹)| = |N(y)|·|N(σ a)|⁻¹` and the norm
--   identity `|N(σ a)| = 𝔑((a))` factor out the constant `𝔑((a))^{-s}`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1469-L1509
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1469-L1509

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
variable {K}

theorem DedekindZeta.GammaIntegral.mellin_mixedGaussian_mul_eq (s : ℂ) {a : 𝓞 K} (ha : a ≠ 0) :
    ∫ x, (mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ s ∂(mixedMulHaar K)
      = (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s) * I K s := by sorry
