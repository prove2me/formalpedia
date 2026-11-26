-- Prove2me | Theorems.Thm_Erdos338Proof_ncard_Iio
-- name    : Erdos338Proof.ncard_Iio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:54.705172+00:00
-- url     : https://prove2.me/theorems/cc17ced6-2bd3-58a0-86f2-7cd9d97961dc
-- title:
--   Erdos338 Proof: ncard Iio
-- statement:
--   The Erdos338 Proof construction uses the ncard Iio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Main.lean#L75-L79
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Main.lean#L75-L79

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

theorem Erdos338Proof.ncard_Iio (b : ℕ) : (Set.Iio b).ncard = b := by sorry
