-- Prove2me | Theorems.Thm_Erdos287_reciprocal_split_repairs_two_blocked_merges
-- name    : Erdos287.reciprocal_split_repairs_two_blocked_merges
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:03:50.656402+00:00
-- url     : https://prove2.me/theorems/12d6dd3a-b20d-551a-88a9-a0e567aab32b
-- title:
--   A reciprocal split can repair two blocked merges
-- statement:
--   For the stated affine family, a minimum-cardinality exact pair cover with the five specified selected denominators and four specified omissions must omit an additional neighbor of one of the five selected denominators. The four inserted denominators have the same reciprocal sum as the five removed denominators.
-- source:
--   Erdős Problem 287. Simultaneous reciprocal edits of cardinality-minimal covers.

import Mathlib

theorem Erdos287.reciprocal_split_repairs_two_blocked_merges (D : Finset ℕ) (m M k : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card) :
    let t := 24871 * k + 4282
    let v := 12540 * k + 2159
    let w := 9996 * k + 1721
    let R : Finset ℕ := {35 * t, 119 * v, 170 * v, 209 * w, 152 * w}
    let A : Finset ℕ := {60 * t, 84 * t, 70 * v, 88 * w}
    let G : Finset ℕ := {35 * t - 1, 35 * t + 1, 119 * v + 1, 209 * w + 1,
      170 * v - 1, 170 * v + 1, 152 * w - 1, 152 * w + 1}
    m < 35 * t → 170 * v ≤ M → R ⊆ D → Disjoint A D →
    ∃ n ∈ G, m ≤ n ∧ n ≤ M ∧ n ∉ D := by sorry
