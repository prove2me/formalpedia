-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_eval_gen_one
-- name    : Autoconvolutions.Blocks.eval_gen_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:28.561913+00:00
-- url     : https://prove2.me/theorems/1ae01f3f-7e41-451e-a56c-ecb09c43b891
-- title:
--   Blocks: eval gen one
-- statement:
--   The Blocks construction uses the eval gen one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockExpansion.lean#L31-L33
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockExpansion.lean#L31-L33

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockExpansion
set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks

theorem Autoconvolutions.Blocks.eval_gen_one {m : ℕ} (D : ℕ) (I : Finset (Fin m)) :
    (gen D I).eval 1 = (I.card : ℝ) := by sorry
