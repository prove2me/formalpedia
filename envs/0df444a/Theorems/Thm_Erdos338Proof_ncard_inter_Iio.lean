-- Prove2me | Theorems.Thm_Erdos338Proof_ncard_inter_Iio
-- name    : Erdos338Proof.ncard_inter_Iio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:34.732251+00:00
-- url     : https://prove2.me/theorems/bcf3e4cc-b515-5ecb-9cb6-fbd590d697b8
-- title:
--   Erdos338 Proof: ncard inter Iio
-- statement:
--   The Erdos338 Proof construction uses the ncard inter Iio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Main.lean#L66-L73
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Main.lean#L66-L73

module
public import Definitions.Def_Erdos338_Pairs
public import Definitions.Def_Erdos338_Residue
public import Definitions.Def_Erdos338_Shift
public import Definitions.Def_Erdos338_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos338Proof

theorem Erdos338Proof.ncard_inter_Iio (S : Set ℕ) (b : ℕ) : (S ∩ Set.Iio b).ncard = cnt S b := by sorry
