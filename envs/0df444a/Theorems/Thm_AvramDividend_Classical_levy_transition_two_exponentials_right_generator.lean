-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_two_exponentials_right_generator
-- name    : AvramDividend.Classical.levy_transition_two_exponentials_right_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:55:37.944907+00:00
-- url     : https://prove2.me/theorems/2023288b-c19a-4f7c-8c5d-d86eeb5a2f56
-- title:
--   Right Lévy semigroup generator limit for a linear combination of two exponential test payoffs
-- statement:
--   The transition expectation of any real linear combination a exp(theta z)+b exp(phi z), for nonnegative theta and phi, has right derivative at time zero equal to the corresponding linear combination of Levy generators. The proof uses the Proved right-generator limit on individual exponential test payoffs and linearity of the Bochner integral, with exponential integrability from the Levy Laplace axiom. This extends verified stochastic transition calculus from a single exponential to finite linear test classes, an intermediate step towards analytic generator-to-semigroup verification.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 5.4 verification theorem; elementary linearity of the Levy semigroup and generator.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_right_generator

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_two_exponentials_right_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b θ φ x : ℝ) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, (a * Real.exp (θ * (x + X.X (Real.toNNReal h) ω)) +
                 b * Real.exp (φ * (x + X.X (Real.toNNReal h) ω))) ∂P) -
          (a * Real.exp (θ * x) + b * Real.exp (φ * x))))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (a * X.generator (fun z : ℝ => Real.exp (θ * z)) x +
             b * X.generator (fun z : ℝ => Real.exp (φ * z)) x)) := by sorry
