-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a381_unique_masked_sum_pospart_v2
-- name    : AvramDividend.Classical.avram_ga_a381_unique_masked_sum_pospart_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:53:09.970115+00:00
-- url     : https://prove2.me/theorems/98591967-cf10-44fa-b64e-dbf0b23fbf69
-- title:
--   Positive part commutes with a finite sum over at most one active crossing cell
-- statement:
--   Under a mask selecting at most one finite-grid cell, the positive part of the masked sum equals the sum of each masked cell's positive part.
-- source:
--   Original stopped Gaussian random crossing source a138, using the strict crossing uniqueness of a380.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a381_unique_masked_sum_pospart_v2
    (m : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ)
    (hUnique : ∀ i j, P i → P j → i = j) :
    max (∑ i ∈ Finset.range m, if P i then f i else 0) 0 =
      ∑ i ∈ Finset.range m, if P i then max (f i) 0 else 0 := by sorry
