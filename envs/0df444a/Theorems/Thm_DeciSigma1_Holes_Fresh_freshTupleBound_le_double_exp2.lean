-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_freshTupleBound_le_double_exp2
-- name    : DeciSigma1.Holes.Fresh.freshTupleBound_le_double_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:11:16.528806+00:00
-- url     : https://prove2.me/theorems/68884716-0f25-49bb-8968-eaf7c687f4ad
-- title:
--   Fresh: fresh Tuple Bound le double exp2
-- statement:
--   The fresh-tuple bound has double exponential growth with a quartic inner polynomial.
--   No positivity assumptions on the tuple size or the number of states are required.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ElementaryBound.lean#L83-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ElementaryBound.lean#L83-L127

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Arithmetic

theorem DeciSigma1.Holes.Fresh.freshTupleBound_le_double_exp2 (k n : ℕ) :
    freshTupleBound k n ≤ exp2 (exp2 ((k + n + 16) ^ 4)) := by sorry
