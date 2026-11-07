-- Prove2me | Theorems.Thm_AaronsonAmbainis_Pack_card_blocks
-- name    : AaronsonAmbainis.Pack.card_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:33.853144+00:00
-- url     : https://prove2.me/theorems/07658464-7efd-48de-b386-ef1b1d0d30ee
-- title:
--   Pack: card blocks
-- statement:
--   The number of blocks of the family `Σ S, Fin (k S)` which contain `i`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Blocks.lean#L21-L28
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Blocks.lean#L21-L28

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Blocks
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Pack.card_blocks (k : Finset ι → ℕ) (i : ι) :
    (univ.filter fun b : (Σ S : Finset ι, Fin (k S)) => i ∈ b.1).card
      = ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), k S := by sorry
