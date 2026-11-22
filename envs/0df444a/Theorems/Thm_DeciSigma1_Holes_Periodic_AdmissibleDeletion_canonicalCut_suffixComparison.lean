-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_suffixComparison
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_suffixComparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:16.302612+00:00
-- url     : https://prove2.me/theorems/3c98e98f-6950-4782-8f4f-d7fad84245f4
-- title:
--   Admissible Deletion: canonical Cut suffix Comparison
-- statement:
--   A comparison of edited texts between canonical cuts, with no deleted block of a piece that
--   starts at or before either cut inside the window, is a comparison of original texts at the
--   canonical cuts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L406-L521
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L406-L521

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}
variable (hx : AdmissibleDeletion W ρ N x)
include hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_suffixComparison (hN : 0 < N) (i j : Fin k) (m : ℕ) :
    ∀ ct' ch', (editedTuple W ρ N x j).length - ct' = m → ct' ≤ (editedTuple W ρ N x j).length →
      SuffixComparison (editedTuple W ρ N x j) ct' (editedTuple W ρ N x i) ch' →
          hx.NoInteriorJunction j ct' m →
      hx.NoInteriorJunction i ch' m → ∀ ct ch,
        CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) j ct ct' →
        CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) i ch ch' →
      SuffixComparison (W j) ct (W i) ch := by sorry
