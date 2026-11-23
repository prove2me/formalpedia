-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_integrable_mixedGaussian_mul_norm_cpow
-- name    : DedekindZeta.GammaIntegral.integrable_mixedGaussian_mul_norm_cpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:47:28.969275+00:00
-- url     : https://prove2.me/theorems/c9ef6832-f08c-4850-afdb-13c96c64557e
-- title:
--   Gamma Integral: integrable mixed Gaussian mul norm cpow
-- statement:
--   **Integrability of the whole-space shifted Gaussian Mellin integrand**
--   (the standard treatment).  For `1 < Re s` and nonzero `a`, the single shifted Minkowski
--   Gaussian times norm-power `x ↦ g(x·σ a)·|N x|^s` is `mixedMulHaar`-integrable on
--   `K_ℝ^*`.  This is the integrability hypothesis required to feed the whole-space
--   Mellin integral `mellin_mixedGaussian_mul_eq` into the fundamental-domain
--   `IsFundamentalDomain.integral_eq_tsum''`/`hasSum_integral_measure` machinery used
--   by the single-orbit collapse `cone_integral_orbit_collapse`.
--
--   Route: the right translation `x ↦ x·σ a` is `mixedMulHaar`-measure-preserving
--   (`mulHaar_integral_comp_mul_right` infrastructure / `mixedMulHaar_map_mul_right`),
--   so integrability reduces to that of `y ↦ g(y)·|N(y·σ(a)⁻¹)|^s`; the latter
--   factors as `𝔑((a))^{-Re s}·(g(y)·|N y|^s)`, integrable by
--   `integrable_gaussian_mellin` (the `gaussian`/`mulHaar` form) transported through
--   the `mixedGaussian`/`mixedMulHaar` identifications.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1527-L1572
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1527-L1572

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
set_option maxHeartbeats 1000000
variable {K}

theorem DedekindZeta.GammaIntegral.integrable_mixedGaussian_mul_norm_cpow (s : ℂ) (hs : 1 < s.re)
    {a : 𝓞 K} (ha : a ≠ 0) :
    Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedMulHaar K) := by sorry
