-- Prove2me | Theorems.Thm_Erdos287_n0_two_impossible
-- name    : Erdos287.n0_two_impossible
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T16:34:48.724435+00:00
-- url     : https://prove2.me/theorems/ae744fac-1036-4047-8da8-73965b2a77f7
-- title:
--   No gap-<=2 representation of 1 starts at denominator 2
-- statement:
--   There is no representation 1 = sum_{i<k} 1/f(i) with 1 < f(0) < f(1) < ..., consecutive gaps f(i+1) - f(i) <= 2, and f(0) = 2. Proof idea: f(1) is 3 or 4. If f(1) = 3, the remaining tail sums to 1/6 yet is at least 1/f(2) >= 1/5. If f(1) = 4 and f(2) = 5, the tail is 1/20 yet at least 1/f(3) >= 1/7; if f(2) = 6, the tail is 1/12 yet at least 1/8. Every case contradicts positivity of the omitted tail terms. Base case of the finite case-check program eliminating small starting denominators for Erdos287.mixed_gap_core.
-- source:
--   Decomposition of the residual core Erdos287.mixed_gap_core (Erdos problem #287); finite case check.

import Mathlib

namespace Erdos287
theorem n0_two_impossible (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : Finset.sum (Finset.range k) (fun i => (1 : ℚ) / (f i : ℚ)) = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hf0 : f 0 = 2) :
    False := by sorry
end Erdos287
