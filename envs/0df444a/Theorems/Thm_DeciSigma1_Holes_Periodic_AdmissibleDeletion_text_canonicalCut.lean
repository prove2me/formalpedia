-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_text_canonicalCut
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.text_canonicalCut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:49.088608+00:00
-- url     : https://prove2.me/theorems/6addde26-24fb-4320-b866-31cd08bb9923
-- title:
--   Admissible Deletion: text canonical Cut
-- statement:
--   From a canonical cut, `n` letters of the edited word with no deleted block in
--   `(c', c' + n)` are `n` retained letters of the original word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L640-L661
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L640-L661

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.text_canonicalCut {l : Fin k} {c c' n : ℕ} (hc :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c')
    (hn : c' + n ≤ (editedTuple W ρ N x l).length)
    (hJ : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
          (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n)) :
    (∀ i < n, c + i ∉ deletedPositions W ρ N x l ∧ c + i < (W l).length) ∧
      keepCut W ρ N x l (c + n) = c' + n ∧
      ∀ i < n, (W l)[c + i]? = (editedTuple W ρ N x l)[c' + i]? := by sorry
