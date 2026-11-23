-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_cone_integral_orbit_collapse
-- name    : DedekindZeta.GammaIntegral.cone_integral_orbit_collapse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:47:42.331635+00:00
-- url     : https://prove2.me/theorems/10c15fbd-098e-44be-9846-e754e839a3d1
-- title:
--   Gamma Integral: cone integral orbit collapse
-- statement:
--   **Step 3 / single-orbit collapse** (the standard analytic argument).  For a fixed
--   nonzero `a₀ : 𝓞 K`, the sum over the full unit group `(𝓞 K)ˣ` of the cone
--   integrals of `g(x·σ(u·a₀))·|N x|^s` collapses to `w_K · I(s) · 𝔑((a₀))^{-s}`.
--
--   This is the analytic heart of the fundamental-cone collapse: the map
--   `u ↦ ↑u · a₀` is injective (domain, `a₀ ≠ 0`) with image the `𝓞ˣ`-orbit
--   generating the principal ideal `span {a₀}`; `g(x·σ(↑u·a₀)) = g((u • x)·σ a₀)`
--   and `|N (u • x)| = |N x|` (`idealThetaKernel_mul_norm_cpow_unitSMul` /
--   `norm_unitSMul`), so each torsion coset contributes the whole-space integral
--   `∫_{K_ℝ^*} g(x·σ a₀)·|N x|^s d*x = 𝔑((a₀))^{-s}·I(s)`
--   (`mellin_mixedGaussian_mul_eq`), summed via the fundamental-cone
--   `IsFundamentalDomain` (`isFundamentalDomain_fundamentalCone`,
--   `IsFundamentalDomain.integral_eq_tsum`) over the free unit complement, times the
--   `w_K = torsionOrder K` torsion cosets.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1809-L1996
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1809-L1996

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
open scoped Pointwise
variable {K}

theorem DedekindZeta.GammaIntegral.cone_integral_orbit_collapse (s : ℂ) (hs : 1 < s.re)
    {a₀ : RingOfIntegers K} (ha₀ : a₀ ≠ 0) :
    ∑' u : (RingOfIntegers K)ˣ,
          ∫ x, (mixedEmbedding.fundamentalCone K).indicator
              (fun x => (mixedGaussian K
                  (x * mixedEmbedding K
                    (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K)) : ℂ)
                * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K)
      = (Units.torsionOrder K : ℂ) * I K s *
          (Ideal.absNorm (Ideal.span {a₀}) : ℂ) ^ (-s) := by sorry
