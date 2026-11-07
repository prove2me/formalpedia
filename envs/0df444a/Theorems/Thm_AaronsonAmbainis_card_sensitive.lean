-- Prove2me | Theorems.Thm_AaronsonAmbainis_card_sensitive
-- name    : AaronsonAmbainis.card_sensitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:12.182529+00:00
-- url     : https://prove2.me/theorems/c0c47863-393c-4bb1-a022-537aef6a92ed
-- title:
--   Aaronson Ambainis: card sensitive
-- statement:
--   The points where flipping `j` changes `g` are twice the bichromatic `j`-edges.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Overlap.lean#L89-L121
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Overlap.lean#L89-L121

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.card_sensitive (g : Cube ι → Bool) (j : ι) :
    (univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x).card = 2 * bdry g j := by sorry
