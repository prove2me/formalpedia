-- Prove2me | Theorems.Thm_AvramDividend_Classical_counting_delta_l1_l2_norm_one
-- name    : AvramDividend.Classical.counting_delta_l1_l2_norm_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:38:14.970807+00:00
-- url     : https://prove2.me/theorems/bd07d151-a315-4547-966e-393eefcd2042
-- title:
--   Moving singleton on counting measure has unit L1 and L2 norms
-- statement:
--   Every singleton indicator on the natural-number counting measure has both L1 and L2 seminorm equal to one. This provides an exact uniform norm bound for the explicit counterexample to unrestricted expectation convergence.
-- source:
--   Explicit finite-band norm equality under counting measure; cited in Avram arbitrary-measure Vitali assumption audit

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.counting_delta_l1_l2_norm_one :
    ∀ n : ℕ,
      eLpNorm (({n} : Set ℕ).indicator (fun _ => (1 : ℝ))) 1
        (Measure.count : Measure ℕ) = 1 ∧
      eLpNorm (({n} : Set ℕ).indicator (fun _ => (1 : ℝ))) 2
        (Measure.count : Measure ℕ) = 1 := by sorry
