-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_periodicOn
-- name    : DeciSigma1.Holes.Periodic.Piece.periodicOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:23.320193+00:00
-- url     : https://prove2.me/theorems/0016ff76-891e-4cb5-83b0-6936d300b8d4
-- title:
--   Piece: periodic On
-- statement:
--   The Piece construction uses the periodic On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L90-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L90-L90

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

theorem DeciSigma1.Holes.Periodic.Piece.periodicOn (P : Piece W d) : PeriodicOn (W P.coordinate) d P.start P.stop := by sorry
