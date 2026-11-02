-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_grid_large_increment_sum_le
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_grid_large_increment_sum_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:24:02.864816+00:00
-- url     : https://prove2.me/theorems/cdbe38cd-eb32-4aeb-a09b-cd0c4c32ac8f
-- title:
--   Original bounded-variation Lévy residual: sum of large grid losses is bounded by terminal loss
-- statement:
--   For the actual source process X and its actual BV physical drift, almost surely on the original probability space, the sum over any uniform finite time grid of the residual increments exceeding any fixed threshold M is bounded by the terminal accumulated residual on the event that the latter exceeds M, and vanishes otherwise. No independent process or assumed jump representation is used. This is a genuine pathwise domination ingredient for obtaining uniform first-moment tails of R_h/h in the unproved global C1 transition-generator theorem.
-- source:
--   Exact source in candidates/work_on/AvramDividend_04c_actual_residual_grid_tail_probe.lean, remotely private-probe compiler-verified, not yet proof-submitted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_grid_large_increment_sum_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (h : ℝ≥0) (n : ℕ) (M : ℝ) :
    ∀ᵐ ω ∂P,
      (∑ i ∈ Finset.range n,
        if M < ((↑((i+1 : ℕ) : ℝ≥0) * h : ℝ) * X.drift -
                X.X (((i+1 : ℕ) : ℝ≥0) * h) ω) -
               (((i : ℝ≥0) * h : ℝ) * X.drift -
                X.X ((i : ℝ≥0) * h) ω)
        then ((↑((i+1 : ℕ) : ℝ≥0) * h : ℝ) * X.drift -
                X.X (((i+1 : ℕ) : ℝ≥0) * h) ω) -
               (((i : ℝ≥0) * h : ℝ) * X.drift -
                X.X ((i : ℝ≥0) * h) ω)
        else 0)
      ≤ if M < (((n : ℝ≥0) * h : ℝ) * X.drift -
                   X.X ((n : ℝ≥0) * h) ω)
         then (((n : ℝ≥0) * h : ℝ) * X.drift -
                   X.X ((n : ℝ≥0) * h) ω)
         else 0 := by sorry
