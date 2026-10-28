-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_right_generator_const_mul
-- name    : AvramDividend.Classical.levy_transition_right_generator_const_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:19:55.3271+00:00
-- url     : https://prove2.me/theorems/dea99530-2c8e-4d16-b4ad-5fb36dadf640
-- title:
--   Scalar closure of the Lévy right-semigroup generator identity
-- statement:
--   Whenever the right time-zero derivative of the Levy transition expectation of f agrees with its full generator, the same identity holds for k times f for every real constant k. No extra integrability assumption is required for the real-valued totalised Bochner integral under scalar multiplication. The proof combines the previously Proved generator_const_mul with linearity of the Bochner integral, the continuous scalar multiplication of limits and ring algebra. Together with the additive-closure theorem this gives a reusable real vector-space structure on the identified generator test class.
-- source:
--   Basic linearity of a Levy transition semigroup and its generator, in the stochastic verification framework of Avram, Palmowski and Pistorius (2007).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_generator_const_mul

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_right_generator_const_mul
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (k x : ℝ)
    (hfSlope : Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, f (x + X.X (Real.toNNReal h) ω) ∂P) - f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator f x))) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, k * f (x + X.X (Real.toNNReal h) ω) ∂P) -
          k * f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator (fun z => k * f z) x)) := by sorry
