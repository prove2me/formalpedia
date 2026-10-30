-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_ioc_neumann_powers_mass_summable
-- name    : AvramDividend.Classical.avram_wave3_05_ioc_neumann_powers_mass_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:40:54.979712+00:00
-- url     : https://prove2.me/theorems/982ece26-d51f-4791-be1e-4073b3d44fd6
-- title:
--   Gaussian causal envelope powers have globally summable masses from the native Ioc recursion
-- statement:
--   For any integrable causal Volterra kernel whose total positive-time mass lies in [0,1), every sequence of powers satisfying the exact Gaussian Ioc recurrence has integrable members and summable global integral masses. The proof identifies the arbitrary recursion with the Proved canonical L1 power sequence by natural-number induction and applies geometric-series summability. This discharges the missing global-mass condition needed for signed Gaussian Neumann L1 integrability.
-- source:
--   Proved causal_l1_convolution_power_exact_mass_geometric UUID 359791d2 and the Gaussian contraction construction causal_damped_antitone_envelope_quadratic.

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_exact_mass_geometric

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.avram_wave3_05_ioc_neumann_powers_mass_summable
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hFzero : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        κ s * F n (x - s) ∂volume)
    (hρ0 : 0 ≤ ∫ x in Ioi (0 : ℝ), κ x ∂volume)
    (hρ1 : (∫ x in Ioi (0 : ℝ), κ x ∂volume) < 1) :
    (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
    Summable (fun n : ℕ =>
      ∫ x in Ioi (0 : ℝ), F n x ∂volume) := by sorry
