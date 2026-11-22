-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_runPrefix_add_mul
-- name    : DeciSigma1.Holes.Periodic.Piece.runPrefix_add_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:15.404683+00:00
-- url     : https://prove2.me/theorems/6e5689fe-b644-44ec-9f89-931e29549052
-- title:
--   Piece: run Prefix add mul
-- statement:
--   The Piece construction uses the run Prefix add mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L58-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L58-L75

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
omit [DecidableEq α]

theorem DeciSigma1.Holes.Periodic.Piece.runPrefix_add_mul [Fintype S] (T : Table α S k) {d : ℕ} (P : Piece W d) {o m : ℕ}
    (ho : Fintype.card S * d ≤ o) (hm : o + m * (d * (Fintype.card S).factorial) ≤ P.len) :
    T.runPrefix W P.coordinate (P.start + o + m * (d * (Fintype.card S).factorial)) =
        T.runPrefix W P.coordinate (P.start + o) := by sorry
