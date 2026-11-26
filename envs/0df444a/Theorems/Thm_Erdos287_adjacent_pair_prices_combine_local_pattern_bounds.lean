-- Prove2me | Theorems.Thm_Erdos287_adjacent_pair_prices_combine_local_pattern_bounds
-- name    : Erdos287.adjacent_pair_prices_combine_local_pattern_bounds
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T16:17:17.696036+00:00
-- url     : https://prove2.me/theorems/97851c63-9025-59b4-8839-790343df15b8
-- title:
--   Adjacent-pair prices combine local residue bounds
-- statement:
--   Let $D$ be selected positions and $E$ be starts of adjacent pairs each containing a selected position. Give each pair a nonnegative price. On every selected position, suppose the sum of its local weights over all blocks containing it equals its target weight plus the prices of the pairs containing it. If each block has a local upper bound on its selected weight, then the total target weight plus every pair price is at most the sum of the local bounds. Blocks may overlap.
-- source:
--   Erdős #287 coupled prime-power exclusion.

import Mathlib
open Finset

theorem Erdos287.adjacent_pair_prices_combine_local_pattern_bounds {ι R : Type} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    (G : Finset ι) (D E : Finset ℕ)
    (w price : ℕ → R) (localWeight : ι → ℕ → R) (upper : ι → R)
    (hprice : ∀ e ∈ E, 0 ≤ price e)
    (hcover : ∀ e ∈ E, e ∈ D ∨ e + 1 ∈ D)
    (hweight : ∀ n ∈ D, (∑ j ∈ G, localWeight j n) = w n +
      ∑ e ∈ E, ((if n = e then price e else 0) + (if n = e + 1 then price e else 0)))
    (hupper : ∀ j ∈ G, (∑ n ∈ D, localWeight j n) ≤ upper j) :
    (∑ n ∈ D, w n) + (∑ e ∈ E, price e) ≤ ∑ j ∈ G, upper j := by sorry
