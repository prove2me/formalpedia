-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_unique
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:45:18.826355+00:00
-- url     : https://prove2.me/theorems/97e42e96-f530-4960-ab68-a62a7ecbed9b
-- title:
--   Admissible Deletion: canonical Cut unique
-- statement:
--   The Admissible Deletion construction uses the canonical Cut unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L532-L542
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L532-L542

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
omit hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_unique {l : Fin k} {c₁ c₂ c' : ℕ} (h₁ :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c₁ c')
    (h₂ : CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c₂ c') :
    c₁ = c₂ := by sorry
