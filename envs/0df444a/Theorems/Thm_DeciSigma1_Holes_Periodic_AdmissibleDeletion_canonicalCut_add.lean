-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_add
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:51.787093+00:00
-- url     : https://prove2.me/theorems/b7b7b852-ea64-4977-bb8d-41d06217061d
-- title:
--   Admissible Deletion: canonical Cut add
-- statement:
--   With no junction in `(c', c' + n]` either, the cut `n` letters later is again canonical, and
--   the `n` letters in between are original letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L665-L678
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L665-L678

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_add {l : Fin k} {c c' n : ℕ} (hc :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c')
    (hn : c' + n ≤ (editedTuple W ρ N x l).length)
    (hJ : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
          (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + (n + 1))) :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l (c + n) (c' + n) ∧
      ∀ i < n, (W l)[c + i]? = (editedTuple W ρ N x l)[c' + i]? := by sorry
