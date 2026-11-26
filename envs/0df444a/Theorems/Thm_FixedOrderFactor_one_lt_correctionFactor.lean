-- Prove2me | Theorems.Thm_FixedOrderFactor_one_lt_correctionFactor
-- name    : FixedOrderFactor.one_lt_correctionFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:05:48.378092+00:00
-- url     : https://prove2.me/theorems/bf21177b-b8fc-56cd-8fe1-78ff8b61c33b
-- title:
--   Fixed Order Factor: one lt correction Factor
-- statement:
--   The Fixed Order Factor construction uses the one lt correction Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L77-L79
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L77-L79

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.one_lt_correctionFactor (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    1 < correctionFactor N r := by sorry
