-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_quadratic_lower_from_compensated_negative_jumps
-- name    : AvramDividend.Classical.psi_quadratic_lower_from_compensated_negative_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T21:06:15.70029+00:00
-- url     : https://prove2.me/theorems/97e86a26-c9f2-497c-92cb-e9f05afd2ff5
-- title:
--   Quadratic lower bound for the spectrally negative Lévy exponent without an unknown compensated integral
-- statement:
--   For the spectrally negative Lévy triplet and θ≥0, show ψ(θ)≥cθ + σ²θ²/2 − ν((−∞,−1]). Use a previously proved lower bound for the compensated exponent, nonnegativity of exp(θy)−1−θy, and integrability of the large-jump mass. No Standing or first-moment assumption is needed.
-- source:
--   Canonical Levy-Khintchine representation and Prove2Me proved bounds psi_lower_bound_by_compensated_small_jumps and levy_large_negative_jump_unit_integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_lower_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.psi_quadratic_lower_from_compensated_negative_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 -
      (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) ≤ X.ψ θ := by sorry
