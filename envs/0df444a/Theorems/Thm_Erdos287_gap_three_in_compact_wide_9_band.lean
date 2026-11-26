-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_9_band
-- name    : Erdos287.gap_three_in_compact_wide_9_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:00:41.191266+00:00
-- url     : https://prove2.me/theorems/f7b36c1b-b381-56ea-a205-86e1530133c8
-- title:
--   Compact Lucas certificates for wide band 9
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[171263047019454982187902002972189565750774750531772130904218567038142881202301234376428697124127793733990087232756415489182395269131,136559784184233651339964983168638167802625998357313169802851241637946516165847788502240036591291824531654297049080916930261764820795589719490570]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide9.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_9_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 171263047019454982187902002972189565750774750531772130904218567038142881202301234376428697124127793733990087232756415489182395269131 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 136559784184233651339964983168638167802625998357313169802851241637946516165847788502240036591291824531654297049080916930261764820795589719490570) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
