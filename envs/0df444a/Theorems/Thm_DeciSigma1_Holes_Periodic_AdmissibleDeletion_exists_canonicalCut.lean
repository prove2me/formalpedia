-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_exists_canonicalCut
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.exists_canonicalCut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:39.060873+00:00
-- url     : https://prove2.me/theorems/ee9ef967-a2b5-4405-812d-26def3a0abb0
-- title:
--   Admissible Deletion: exists canonical Cut
-- statement:
--   Every cut of an edited word has a canonical original cut: its greatest preimage.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L517-L522
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L517-L522

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.exists_canonicalCut (l : Fin k) {c' : ℕ} (hc' : c' ≤ (editedTuple W ρ N x l).length) :
    ∃ c, CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c' := by sorry
