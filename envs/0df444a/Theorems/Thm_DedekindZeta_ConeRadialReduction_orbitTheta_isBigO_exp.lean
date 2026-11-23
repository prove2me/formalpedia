-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_orbitTheta_isBigO_exp
-- name    : DedekindZeta.ConeRadialReduction.orbitTheta_isBigO_exp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:06.976301+00:00
-- url     : https://prove2.me/theorems/73c07405-db86-456c-834b-8e10fb3a6d6c
-- title:
--   Cone Radial Reduction: orbit Theta is Big O exp
-- statement:
--   **Gaussian tail of the orbit-integrated theta** (the analytic crux): there
--   are `c, α > 0` with `orbitTheta K 𝔞 r =O[atTop] e^{-c r^α}`. After the radial
--   blow-up `radialMap K r σ = r^{1/d} • σ`, the Minkowski Gaussian summands of
--   `idealThetaKernel` scale as `exp(-π r^{2/d} · Q(σ·a))`, so the whole kernel — and
--   its integral over the finite-measure compact surface slice — decays like a
--   Gaussian with `α = 2/[K:ℚ]`. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1814-L1858
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1814-L1858

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem DedekindZeta.ConeRadialReduction.orbitTheta_isBigO_exp (𝔞 : Ideal (𝓞 K)) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (fun r : ℝ => orbitTheta K 𝔞 r) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) := by sorry
