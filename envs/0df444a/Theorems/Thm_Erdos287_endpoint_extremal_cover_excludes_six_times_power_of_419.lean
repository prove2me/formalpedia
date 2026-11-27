-- Prove2me | Theorems.Thm_Erdos287_endpoint_extremal_cover_excludes_six_times_power_of_419
-- name    : Erdos287.endpoint_extremal_cover_excludes_six_times_power_of_419
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:33:01.908192+00:00
-- url     : https://prove2.me/theorems/997fedcf-fa69-5ded-b000-ed19b25f6c7b
-- title:
--   An extremal cover cannot start at six times a power of 419 in the stated range
-- statement:
--   Let $t=419^j$ with $j\ge1$. An endpoint-extremal exact adjacent-pair cover cannot have smallest denominator $6t$ and maximum $M$ with $15t\le M<18t$.
-- source:
--   Erdős Problem 287. Endpoint trimming combined with a cofactor residue test.

import Mathlib

theorem Erdos287.endpoint_extremal_cover_excludes_six_times_power_of_419 (D : Finset ℕ) (M j : ℕ) (hj : 1 ≤ j) :
    let t := 419 ^ j
    let m := 6 * t
    m ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) →
    15 * t ≤ M → M < 18 * t → False := by sorry
