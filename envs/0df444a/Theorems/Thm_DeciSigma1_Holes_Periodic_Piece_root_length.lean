-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_root_length
-- name    : DeciSigma1.Holes.Periodic.Piece.root_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:27.651944+00:00
-- url     : https://prove2.me/theorems/d5a95ad5-ce4c-4158-bd26-729c2f303c55
-- title:
--   Piece: root length
-- statement:
--   The Piece construction uses the root length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L102-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L102-L103

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

theorem DeciSigma1.Holes.Periodic.Piece.root_length (P : Piece W d) : P.root.length = d := by sorry
