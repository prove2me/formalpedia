-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_suffixComparison_lift
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.suffixComparison_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:48.418839+00:00
-- url     : https://prove2.me/theorems/f1bdf0e7-d6a0-44a5-9f4e-37a34d31cd7a
-- title:
--   Admissible Deletion: suffix Comparison lift
-- statement:
--   Every comparison of the edited tuple lifts to a comparison of the original tuple whose
--   start states are the same.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L819-L830
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L819-L830

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.suffixComparison_lift {S : Type} [Fintype S] (T : Table α S k) (hNS : N = Fintype.card S)
    (hN : 0 < N) (i j : Fin k) {a' b' : ℕ} (ha' : a' ≤ (editedTuple W ρ N x i).length)
    (hb' : b' ≤ (editedTuple W ρ N x j).length)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a') :
    ∃ a ≤ (W i).length, ∃ b ≤ (W j).length, SuffixComparison (W j) b (W i) a ∧
      T.runPrefix W i a = T.runPrefix (editedTuple W ρ N x) i a' ∧ T.runPrefix W j b =
          T.runPrefix (editedTuple W ρ N x) j b' := by sorry
