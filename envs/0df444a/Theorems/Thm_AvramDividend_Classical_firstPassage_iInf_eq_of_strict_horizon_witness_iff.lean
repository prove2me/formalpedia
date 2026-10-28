-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff
-- name    : AvramDividend.Classical.firstPassage_iInf_eq_of_strict_horizon_witness_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:34:32.783688+00:00
-- url     : https://prove2.me/theorems/92726415-3249-44ca-b210-3790cce4b6fe
-- title:
--   Extended first-passage clocks coincide when all strict-horizon crossing witnesses coincide
-- statement:
--   Two extended-real first-passage clocks defined as infima of possibly different families of candidate crossing times are equal if, for every extended horizon T, one family has a witness strictly before T exactly when the other has a witness strictly before T. This order-theoretic bridge connects countable-grid crossing-time detection to the continuous-time strict passage clocks in the renewal proof.
-- source:
--   Mathlib.Order.CompleteLattice.Defs iInf_lt_iff and iInf_le. Supports using Proved chat03_upper_before_horizon_countable_grid_iff and its lower companion to identify countable full-path reward clocks with true Lévy passage clocks, for lower-bound UUID 6b821aa5-c792-4436-8eca-fc9429115ef9.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Defs

open scoped ENNReal

theorem AvramDividend.Classical.firstPassage_iInf_eq_of_strict_horizon_witness_iff
    {ι κ : Sort*} (f : ι → ℝ≥0∞) (g : κ → ℝ≥0∞)
    (h : ∀ T : ℝ≥0∞, (∃ i, f i < T) ↔ (∃ j, g j < T)) :
    (⨅ i, f i) = (⨅ j, g j) := by sorry
