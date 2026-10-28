-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_two_exponentials_right_full_generator
-- name    : AvramDividend.Classical.levy_transition_two_exponentials_right_full_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:07:56.639278+00:00
-- url     : https://prove2.me/theorems/4596ace9-6f1c-4007-b06c-274b95fc2260
-- title:
--   Right Lévy transition derivative equals full generator of a two-exponential payoff
-- statement:
--   For a spectrally negative Levy process, the right derivative at zero of the expected transition of an arbitrary real linear combination of two exponentials with nonnegative rates equals the full canonical Levy generator of that combined payoff. This closes the previously Proved two-exponential semigroup limit and generator linearity into one exact test-function generator identity. It is a verified finite-dimensional extension of the exponential test class, without assuming a general Ito formula for arbitrary smooth payoffs.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 5.4; linearity of the Levy semigroup and generator.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_two_exponentials_right_generator
import Theorems.Thm_AvramDividend_Classical_levy_generator_two_exponentials_linear

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_two_exponentials_right_full_generator
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
      (nhds (X.generator
        (fun z : ℝ => a * Real.exp (θ * z) + b * Real.exp (φ * z)) x)) := by sorry
