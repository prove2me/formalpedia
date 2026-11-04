-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_positive_ruin_excludes_terminal_atom
-- name    : AvramDividend.Classical.avram_p4_e_localise_positive_ruin_excludes_terminal_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:43:33.574637+00:00
-- url     : https://prove2.me/theorems/91acbeb6-782d-4d76-b331-003bfb016e54
-- title:
--   Original closed Stieltjes horizon includes time zero but excludes a positive ruin endpoint
-- statement:
--   At the exact positive physical ruin time, the canonical source paymentTimes restriction retains the time-zero payment while excluding a right dividend atom at ruin, despite intersection with the closed upper time interval Iic. This is a set-theoretic property of the actual source convention, independent of the original process regularity. It prevents incorrect inclusion of a ruin-time payment in the localised budget and does not discard fixed-horizon pre-ruin atoms.
-- source:
--   Original Avram DividendStrategy.paymentTimes definition and the source finite-positive ruin endpoint convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_positive_ruin_excludes_terminal_atom
    (σ : ℝ≥0∞) (t : ℝ≥0)
    (ht : 0 < t) (hruin : (t : ℝ≥0∞) = σ) :
    (0 : ℝ) ∈ paymentTimes σ ∩ Iic (t : ℝ) ∧
    (t : ℝ) ∉ paymentTimes σ ∩ Iic (t : ℝ) := by sorry
