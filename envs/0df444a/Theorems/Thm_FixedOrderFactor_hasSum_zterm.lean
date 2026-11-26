-- Prove2me | Theorems.Thm_FixedOrderFactor_hasSum_zterm
-- name    : FixedOrderFactor.hasSum_zterm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:48.547361+00:00
-- url     : https://prove2.me/theorems/297b4673-cf59-41e0-ac9e-1afef7a3e00d
-- title:
--   Fixed Order Factor: has Sum zterm
-- statement:
--   The Fixed Order Factor construction uses the has Sum zterm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L25-L27
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L25-L27

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.hasSum_zterm (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    HasSum (zterm N s) (zetaN N s) := by sorry
