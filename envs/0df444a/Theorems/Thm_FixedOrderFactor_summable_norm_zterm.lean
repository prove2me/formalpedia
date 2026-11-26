-- Prove2me | Theorems.Thm_FixedOrderFactor_summable_norm_zterm
-- name    : FixedOrderFactor.summable_norm_zterm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:11.181455+00:00
-- url     : https://prove2.me/theorems/098429a4-e31f-5d32-8081-086b19da9ef2
-- title:
--   Fixed Order Factor: summable norm zterm
-- statement:
--   The Fixed Order Factor construction uses the summable norm zterm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L29-L32
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L29-L32

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.summable_norm_zterm (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n => ‖zterm N s n‖) := by sorry
