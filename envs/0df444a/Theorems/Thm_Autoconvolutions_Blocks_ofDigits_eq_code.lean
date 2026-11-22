-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_ofDigits_eq_code
-- name    : Autoconvolutions.Blocks.ofDigits_eq_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:54.932729+00:00
-- url     : https://prove2.me/theorems/7b00295a-5e09-49d4-84bf-9938dad09f77
-- title:
--   Blocks: of Digits eq code
-- statement:
--   The Blocks construction uses the of Digits eq code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L44-L55
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L44-L55

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockKeys
set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Blocks
open Finset

theorem Autoconvolutions.Blocks.ofDigits_eq_code {m D : ℕ} (a : Fin m → ℕ) :
    Nat.ofDigits D (List.ofFn a) = code D a := by sorry
