-- Prove2me | Theorems.Thm_Erdos287_no_joint_endpoint_family_at_137830156202054919616193
-- name    : Erdos287.no_joint_endpoint_family_at_137830156202054919616193
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T01:17:59.644573+00:00
-- url     : https://prove2.me/theorems/875075ee-922f-5663-9310-a1e31897723c
-- title:
--   Joint endpoint trimming excludes the 20-to-55 prime-power family
-- statement:
--   No endpoint-extremal pair cover has minimum $20p^e$ and maximum $55p^e$ for $p=137830156202054919616193$ and $e\ge1$.
-- source:
--   Erdős Problem 287. The extremal endpoint cover reduction.

import Mathlib

theorem Erdos287.no_joint_endpoint_family_at_137830156202054919616193 (D : Finset ℕ) (e : ℕ) (he : 1 ≤ e) :
    let t := 137830156202054919616193 ^ e
    let m := 20 * t
    let M := 55 * t
    m ∈ D → M ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) → False := by sorry
