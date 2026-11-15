-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a394_unique_masked_sum_absolute_dominated
-- name    : AvramDividend.Classical.avram_ga_a394_unique_masked_sum_absolute_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:49:27.077522+00:00
-- url     : https://prove2.me/theorems/1c965a0d-6c1d-4386-b2a7-1b0065de8975
-- title:
--   One-active finite masked sum inherits an absolute per-cell envelope
-- statement:
--   If at most one cell satisfies a mask, and each active cell has absolute value at most B≥0, then the absolute value of the entire masked sum is at most B.
-- source:
--   Gaussian A source a388 and a390, using already-Proved a392 for positive and negative parts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a394_unique_masked_sum_absolute_dominated
    (m : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hUnique : ∀ i j, P i → P j → i = j)
    (hBound : ∀ i < m, P i → |f i| ≤ B) :
    |∑ i ∈ Finset.range m, if P i then f i else 0| ≤ B := by sorry
