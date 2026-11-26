-- Prove2me | Theorems.Thm_Erdos287_single_period_distance_packing
-- name    : Erdos287.single_period_distance_packing
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:12:45.590343+00:00
-- url     : https://prove2.me/theorems/84b63342-4eb5-4570-a5bd-9a452b26668a
-- title:
--   Sharp forbidden-distance packing on one interval
-- statement:
--   Let u and v be nonnegative integers with u positive and 2u at most v+2. Any subset of the integers from 0 through u+v-1 avoiding all positive pairwise differences in the closed interval [u,v] has at most u elements. The initial u integers attain the bound.
-- source:
--   Erdős Problem #287, exact finite packing bound for groups of affine prime forms.

import Mathlib

theorem Erdos287.single_period_distance_packing (u v : ℕ) (S : Finset ℕ) (hu : 0 < u) (hv : 2 * u ≤ v + 2)
    (hS : ∀ s ∈ S, s < u + v)
    (havoid : ∀ x ∈ S, ∀ y ∈ S, u ≤ y - x → v < y - x) : S.card ≤ u := by sorry
