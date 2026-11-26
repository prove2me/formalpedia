-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_8_band
-- name    : Erdos287.gap_three_in_compact_wide_8_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:00:47.244776+00:00
-- url     : https://prove2.me/theorems/fa830eb5-3405-4df6-bde5-3c2738834e49
-- title:
--   Compact Lucas certificates for wide band 8
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[214159363982694220762791838234441303966448576564395913178069362933275385011193945334184159829056850097682828246510469131,171263047019454982187902002972189565750774750531772130904218567038142881202301234376428697124127793733990087232756415489182395269130]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide8.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_8_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 214159363982694220762791838234441303966448576564395913178069362933275385011193945334184159829056850097682828246510469131 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 171263047019454982187902002972189565750774750531772130904218567038142881202301234376428697124127793733990087232756415489182395269130) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
