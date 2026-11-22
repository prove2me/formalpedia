-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_start_lt_stop
-- name    : DeciSigma1.Holes.Periodic.Piece.start_lt_stop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:23.917547+00:00
-- url     : https://prove2.me/theorems/df18673c-798f-4b7d-b90c-2d4b93dd0a9c
-- title:
--   Piece: start lt stop
-- statement:
--   The Piece construction uses the start lt stop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L99-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L99-L100

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.Piece
variable {W : Fin k → List α} {d : ℕ}

theorem DeciSigma1.Holes.Periodic.Piece.start_lt_stop (P : Piece W d) :
    P.start < P.stop := by sorry
