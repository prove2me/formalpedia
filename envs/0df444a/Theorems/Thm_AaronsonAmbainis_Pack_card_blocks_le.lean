-- Prove2me | Theorems.Thm_AaronsonAmbainis_Pack_card_blocks_le
-- name    : AaronsonAmbainis.Pack.card_blocks_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:37.406475+00:00
-- url     : https://prove2.me/theorems/c0dbd353-7973-49b2-ba25-f11faf67d656
-- title:
--   Pack: card blocks le
-- statement:
--   For `k S = ⌊N κ S⌋₊` and a fractional packing `κ`, every coordinate lies in at most `N`
--   blocks of the family `Σ S, Fin (k S)`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Scaled.lean#L22-L38
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Scaled.lean#L22-L38

import Definitions.Def_AaronsonAmbainis_Pack_Gate
import Definitions.Def_AaronsonAmbainis_Pack_Blocks
import Definitions.Def_AaronsonAmbainis_Pack_Scaled
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
open Finset

theorem AaronsonAmbainis.Pack.card_blocks_le {ι : Type} [Fintype ι] [DecidableEq ι] (κ : Finset ι → ℝ)
    (hκ : ∀ S, 0 ≤ κ S)
    (hpack : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) (N : ℕ) (i : ι) :
    (univ.filter fun b : (Σ S : Finset ι, Fin ⌊(N : ℝ) * κ S⌋₊) => i ∈ b.1).card ≤ N := by sorry
