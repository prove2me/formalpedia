-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_10_band
-- name    : Erdos287.gap_three_in_compact_wide_10_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:01:25.291681+00:00
-- url     : https://prove2.me/theorems/b1c63fe2-60ea-44de-b3e1-e5cc1959e288
-- title:
--   Compact Lucas certificates for wide band 10
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[136559784184233651339964983168638167802625998357313169802851241637946516165847788502240036591291824531654297049080916930261764820795589719490571,103091558235810307556758383984131383502338270262018175758223050084115981815857437218079654870252928856883491762045970221421952527076000397762791792506306555]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide10.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_10_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 136559784184233651339964983168638167802625998357313169802851241637946516165847788502240036591291824531654297049080916930261764820795589719490571 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 103091558235810307556758383984131383502338270262018175758223050084115981815857437218079654870252928856883491762045970221421952527076000397762791792506306555) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
