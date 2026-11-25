-- Prove2me | Theorems.Thm_Erdos684_pred_mod_of_dvd
-- name    : Erdos684.pred_mod_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:19:58.451402+00:00
-- url     : https://prove2.me/theorems/a3313104-3913-4b59-8482-3d55ceb7bc63
-- title:
--   Erdos684: pred mod of dvd
-- statement:
--   The predecessor of a positive multiple has the largest possible residue.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L101-L104
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L101-L104

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite
set_option autoImplicit false
@[expose] public section
public section
open Erdos684

theorem Erdos684.pred_mod_of_dvd {M q : ℕ} (hM : 0 < M) (_hq : 0 < q) (hdiv : q ∣ M) :
    (M - 1) % q = q - 1 := by sorry
