-- Prove2me | Theorems.Thm_FixedOrderFactor_hasSum_coprime_pairs
-- name    : FixedOrderFactor.hasSum_coprime_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:06:09.213391+00:00
-- url     : https://prove2.me/theorems/8112fb9e-f292-4300-a864-775d6fae111d
-- title:
--   Fixed Order Factor: has Sum coprime pairs
-- statement:
--   **Diagonal.** The pairs `(m, n) = (d a^r, d b^r)` with `a, b` coprime are what an average over
--   characters of order `r` keeps; their weights sum to the correction factor.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L57-L62
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L57-L62

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.hasSum_coprime_pairs (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasSum (fun ab : ℕ × ℕ =>
        if 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2
        then 1 / ((ab.1 * ab.2 : ℕ) : ℝ) ^ r else 0)
      (correctionFactor N r) := by sorry
