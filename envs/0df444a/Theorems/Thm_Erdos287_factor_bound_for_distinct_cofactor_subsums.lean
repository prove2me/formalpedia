-- Prove2me | Theorems.Thm_Erdos287_factor_bound_for_distinct_cofactor_subsums
-- name    : Erdos287.factor_bound_for_distinct_cofactor_subsums
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T16:51:01.093682+00:00
-- url     : https://prove2.me/theorems/2264a9d1-c1df-4dc9-a057-1bae4370d025
-- title:
--   Factor bound for distinct cofactor subsums
-- statement:
--   Suppose a finite core of nonnegative integer weights consists of multiples of $d>0$ and has total at most $dK$. Add any finite family of other blocks, each with its own number of distinct subset sums. The number of distinct subset sums of the union is at most $K+1$ times the product of the block counts. The blocks are allowed to overlap.
-- source:
--   Erdős #287 explicit near-linear prime-factor analysis.

import Mathlib
open Finset

theorem Erdos287.factor_bound_for_distinct_cofactor_subsums {ι α : Type} [DecidableEq α] (I : Finset ι) (core : Finset α)
    (A : ι → Finset α) (w : α → ℕ) (d K : ℕ) (hd : 0 < d)
    (hdiv : ∀ a ∈ core, d ∣ w a) (hcap : (∑ a ∈ core, w a) ≤ d * K) :
    let sums := fun S : Finset α => S.powerset.image (fun T => ∑ a ∈ T, w a)
    (sums (core ∪ I.biUnion A)).card ≤ (K + 1) * ∏ j ∈ I, (sums (A j)).card := by sorry
