-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a392_unique_masked_sum_positive_dominated
-- name    : AvramDividend.Classical.avram_ga_a392_unique_masked_sum_positive_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:37:20.194949+00:00
-- url     : https://prove2.me/theorems/8269c1d2-0f55-4133-8ae4-3fcbaf966b7b
-- title:
--   One-active positive finite-mask sum is bounded by its uniform cell bound
-- statement:
--   If a decidable mask selects at most one natural-number index and every active positive part is at most a nonnegative B, then the positive part of the entire masked finite-grid sum is bounded by B.
-- source:
--   Gaussian A a387 and a389 original strict stopping crossing-cell positive bounds; a381 proved masked sum identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a392_unique_masked_sum_positive_dominated
    (m : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hUnique : ∀ i j, P i → P j → i = j)
    (hBound : ∀ i < m, P i → max (f i) 0 ≤ B) :
    max (∑ i ∈ Finset.range m, if P i then f i else 0) 0 ≤ B := by sorry
