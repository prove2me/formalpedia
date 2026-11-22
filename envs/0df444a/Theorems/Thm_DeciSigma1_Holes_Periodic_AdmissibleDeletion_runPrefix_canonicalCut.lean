-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_canonicalCut
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_canonicalCut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:24.566298+00:00
-- url     : https://prove2.me/theorems/dc545828-5b17-4b41-b0ac-b0165e67762d
-- title:
--   Admissible Deletion: run Prefix canonical Cut
-- statement:
--   The Admissible Deletion construction uses the run Prefix canonical Cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L544-L553
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L544-L553

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
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_canonicalCut [Fintype S] (T : Table α S k) (hN : N = Fintype.card S) {l : Fin k}
    {c c' : ℕ} (h :
        CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c') :
    T.runPrefix (editedTuple W ρ N x) l c' =
        T.runPrefix W l c := by sorry
