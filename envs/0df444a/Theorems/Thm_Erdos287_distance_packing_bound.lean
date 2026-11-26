-- Prove2me | Theorems.Thm_Erdos287_distance_packing_bound
-- name    : Erdos287.distance_packing_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:19:04.14165+00:00
-- url     : https://prove2.me/theorems/e0c93903-8cbe-523f-97ac-fc76096e63e5
-- title:
--   Density bound for a finite set avoiding a prescribed interval of differences
-- statement:
--   Let $S\subseteq\{0,\ldots,N-1\}$ and let $u,v$ be positive-scale integer bounds with $u>0$ and $v\ge2u-2$. Suppose no two elements in increasing order have difference in $[u,v]$. Then
--
--   $$
--   (u+v)|S|\le u(N+v).
--   $$
-- source:
--   Elementary difference packing for the affine-form approach to Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.distance_packing_bound (N u v : ℕ) (S : Finset ℕ) (hu : 0 < u) (hv : 2 * u ≤ v + 2)
    (hN : ∀ s ∈ S, s < N)
    (havoid : ∀ x ∈ S, ∀ y ∈ S, u ≤ y - x → v < y - x) :
    (u + v) * S.card ≤ u * (N + v) := by sorry
