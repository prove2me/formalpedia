-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_len_ge
-- name    : DeciSigma1.Holes.Periodic.Piece.len_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:24.442386+00:00
-- url     : https://prove2.me/theorems/21b781eb-43e9-4ac0-9010-a8aa59dcdb41
-- title:
--   Piece: len ge
-- statement:
--   The Piece construction uses the len ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L97-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L97-L97

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

theorem DeciSigma1.Holes.Periodic.Piece.len_ge (P : Piece W d) : 2 * d ≤ P.len := by sorry
