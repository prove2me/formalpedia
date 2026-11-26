-- Prove2me | Theorems.Thm_FixedOrderFactor_correctionFactor_even
-- name    : FixedOrderFactor.correctionFactor_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:06:14.384076+00:00
-- url     : https://prove2.me/theorems/cf7bbeef-90e7-41dc-a9a4-39e00199fe55
-- title:
--   Fixed Order Factor: correction Factor even
-- statement:
--   **Closed form for even order.**
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L65-L69
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L65-L69

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.correctionFactor_even {k : ℕ} (hk : 0 < k) :
    correctionFactor ∅ (2 * k) =
      -((Nat.choose (4 * k) (2 * k) : ℝ) * (bernoulli (2 * k) : ℝ) ^ 2 /
        (2 * (bernoulli (4 * k) : ℝ))) := by sorry
