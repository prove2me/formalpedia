-- Prove2me | Theorems.Thm_FixedOrderFactor_card_char_pow_eq_one
-- name    : FixedOrderFactor.card_char_pow_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:16.569713+00:00
-- url     : https://prove2.me/theorems/73b0e2cd-713a-4b87-954b-d36a242a118c
-- title:
--   Fixed Order Factor: card char pow eq one
-- statement:
--   There are exactly `r` characters modulo `p` with `χʳ = 1` when `r ∣ p - 1`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L128-L130
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L128-L130

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
open Classical

theorem FixedOrderFactor.card_char_pow_eq_one (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : r ∣ p - 1) :
    ((Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1)).card = r := by sorry
