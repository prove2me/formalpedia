-- Prove2me | Theorems.Thm_Erdos287_no_joint_endpoint_family_in_five_prime_classes
-- name    : Erdos287.no_joint_endpoint_family_in_five_prime_classes
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T01:16:30.675886+00:00
-- url     : https://prove2.me/theorems/c0038e47-f0f1-5bd8-9f8c-d525e7bc7b5b
-- title:
--   Five prime residue classes excluded for the 20-to-55 endpoint ratio
-- statement:
--   For every prime $p$ with $2p>171783896431127155981377$ and $p$ congruent to $1,4,6,7,$ or $9$ modulo $11$, no endpoint-extremal exact pair cover has endpoints $20p^e,55p^e$ at any positive exponent.
-- source:
--   Erdős Problem 287. The extremal endpoint cover reduction.

import Mathlib

theorem Erdos287.no_joint_endpoint_family_in_five_prime_classes (D : Finset ℕ) (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hsize : 171783896431127155981377 < 2 * p)
    (hclass : (p : ZMod 11) ∉ ({0, 2, 3, 5, 8, 10} : Finset (ZMod 11))) :
    let m := 20 * p ^ e
    let M := 55 * p ^ e
    m ∈ D → M ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) → False := by sorry
