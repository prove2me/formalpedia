-- Prove2me | Theorems.Thm_Erdos287_compatible_slopes_dyadic_size_bound
-- name    : Erdos287.compatible_slopes_dyadic_size_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:24:50.871009+00:00
-- url     : https://prove2.me/theorems/fa8dc683-c411-46ef-be3f-b52e6bffd9fa
-- title:
--   Dyadic size bound for pairwise compatible affine slopes
-- statement:
--   For positive integers $a<b$ with $b-a\mid a$, the two slopes have different valuations at $2$. If $S$ is a nonempty finite set of positive slopes with this compatibility for every pair, then one of its elements is divisible by $2^{|S|-1}$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.compatible_slopes_dyadic_size_bound :
    (∀ a b : ℕ, 0 < a → a < b → b - a ∣ a → padicValNat 2 a ≠ padicValNat 2 b) ∧
    ∀ S : Finset ℕ, S.Nonempty → (∀ a ∈ S, 0 < a) →
      (∀ a ∈ S, ∀ b ∈ S, a < b → b - a ∣ a) →
      ∃ a ∈ S, 2 ^ (S.card - 1) ∣ a := by sorry
