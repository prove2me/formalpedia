-- Prove2me | Theorems.Thm_FixedOrderFactor_summable_fN
-- name    : FixedOrderFactor.summable_fN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:10.603805+00:00
-- url     : https://prove2.me/theorems/c2689252-e805-5c27-903b-1e27df873ff1
-- title:
--   Fixed Order Factor: summable f N
-- statement:
--   The Fixed Order Factor construction uses the summable f N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L38-L42
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L38-L42

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor

theorem FixedOrderFactor.summable_fN (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n => ‖fN N s (by omega) n‖) := by sorry
