-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_decay_radialTheta
-- name    : DedekindZeta.ConeRadialReduction.exists_decay_radialTheta
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:36.44191+00:00
-- url     : https://prove2.me/theorems/8ddb1db0-9b20-4e11-b7a9-8ac64883c0b0
-- title:
--   Cone Radial Reduction: exists decay radial Theta
-- statement:
--   **Exponential decay of the completed radial theta**: there are `c, α > 0` with
--   `F(𝔞, r) − a₀ = orbitTheta K 𝔞 r = O(e^{-c r^α})` as `r → ∞` (the Gaussian tail
--   of the nonzero lattice points after orbit integration; `α = 2 / [K:ℚ]` from the
--   radial scaling). The same `c, α` work for the dual. Built from the two crux tail
--   bounds `orbitTheta_isBigO_exp`/`orbitThetaFrac_isBigO_exp` (unified to a single
--   `(c, α)` via `exp_isBigO_exp_of_le`), using `radialTheta − V = orbitTheta` and
--   `radialThetaDual − V = orbitThetaFrac (dualIdeal 𝔞)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2348-L2368
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2348-L2368

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

theorem DedekindZeta.ConeRadialReduction.exists_decay_radialTheta (𝔞 : Ideal (𝓞 K)) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (fun r : ℝ => radialTheta K 𝔞 r - surfaceVolume K) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) ∧
      (fun r : ℝ => radialThetaDual K 𝔞 r - surfaceVolume K) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) := by sorry
