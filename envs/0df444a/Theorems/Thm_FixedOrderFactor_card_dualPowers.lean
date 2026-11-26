-- Prove2me | Theorems.Thm_FixedOrderFactor_card_dualPowers
-- name    : FixedOrderFactor.card_dualPowers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:59.250593+00:00
-- url     : https://prove2.me/theorems/4210ba8d-54cd-5835-b50b-fd64e43c10c8
-- title:
--   Fixed Order Factor: card dual Powers
-- statement:
--   The Fixed Order Factor construction uses the card dual Powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L34-L38
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L34-L38

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]

theorem FixedOrderFactor.card_dualPowers {r : ℕ} (hr : r ∣ p - 1) : Nat.card (dualPowers p r) = r := by sorry
