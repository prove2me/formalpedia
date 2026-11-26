-- Prove2me | Theorems.Thm_FixedOrderFactor_summable_prod_zterm
-- name    : FixedOrderFactor.summable_prod_zterm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:24.017933+00:00
-- url     : https://prove2.me/theorems/6f8971e8-525e-5af5-845d-c90f3957ef3a
-- title:
--   Fixed Order Factor: summable prod zterm
-- statement:
--   The Fixed Order Factor construction uses the summable prod zterm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L34-L36
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L34-L36

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.summable_prod_zterm (N : Finset Nat.Primes) {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    Summable (fun x : ℕ × ℕ => zterm N s x.1 * zterm N t x.2) := by sorry
