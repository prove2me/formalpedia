-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
-- name    : DeciSigma1.Holes.Periodic.FollowerEdge.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:16.693477+00:00
-- url     : https://prove2.me/theorems/e1218d0d-b9d8-40f7-9147-3b10268f8fd4
-- title:
--   Follower Edge: symm
-- statement:
--   The Follower Edge construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L233-L235
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L233-L235

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}

theorem DeciSigma1.Holes.Periodic.FollowerEdge.symm {W : Fin k → List α} {d : ℕ} {P Q : Piece W d} (h : FollowerEdge P Q) :
    FollowerEdge Q P := by sorry
