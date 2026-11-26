-- Prove2me | Theorems.Thm_FixedOrderFactor_correctionFactor_succ_lt
-- name    : FixedOrderFactor.correctionFactor_succ_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:05.561566+00:00
-- url     : https://prove2.me/theorems/9f769bbc-0202-4db4-a9bf-e2706b7f5f5f
-- title:
--   Fixed Order Factor: correction Factor succ lt
-- statement:
--   The Fixed Order Factor construction uses the correction Factor succ lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L81-L83
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L81-L83

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.correctionFactor_succ_lt (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N (r + 1) < correctionFactor N r := by sorry
