-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_orbitThetaFrac_isBigO_exp
-- name    : DedekindZeta.ConeRadialReduction.orbitThetaFrac_isBigO_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:49:31.861049+00:00
-- url     : https://prove2.me/theorems/34da9a17-9603-4c2a-8583-85075483705b
-- title:
--   Cone Radial Reduction: orbit Theta Frac is Big O exp
-- statement:
--   **Gaussian tail of the fractional orbit-integrated theta** (the dual case of
--   `orbitTheta_isBigO_exp`): `orbitThetaFrac K I r =O[atTop] e^{-c r^α}` for the
--   fractional ideal `I` (applied below to the dual `Theta.dualIdeal K 𝔞`). Same
--   Gaussian mechanism via `mixedThetaKernel`. The proof integrates the uniform
--   Gaussian bound `mixedThetaKernel_radialMap_isBigO_uniform` over the finite-measure
--   compact surface slice: `‖∫_S Θ_mix‖ ≤ ∫_S ‖Θ_mix‖ ≤ μ_S(S)·B·e^{-c r^α}`, using
--   `integrableOn_mixedThetaKernel_radialMap` and `measure_normEqOneSurface_lt_top`.
--   the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2274-L2317
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2274-L2317

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

theorem DedekindZeta.ConeRadialReduction.orbitThetaFrac_isBigO_exp (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (fun r : ℝ => orbitThetaFrac K I r) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) := by sorry
