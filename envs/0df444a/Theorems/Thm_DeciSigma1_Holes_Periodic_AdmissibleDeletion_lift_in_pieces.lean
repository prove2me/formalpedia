-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_lift_in_pieces
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.lift_in_pieces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:35.798806+00:00
-- url     : https://prove2.me/theorems/6fdad0c0-4e62-47a4-8fe4-8e8920aa5b5b
-- title:
--   Admissible Deletion: lift in pieces
-- statement:
--   A comparison of the edited tuple that starts inside the images of two pieces, at offsets `pT`
--   and `pS`, lifts to a comparison of the original tuple at offsets `oT` and `oS` with the same
--   states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L548-L598
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L548-L598

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.lift_in_pieces {S : Type} [Fintype S] (T : Table α S k) (hNS : N = Fintype.card S)
    {i j : Fin k} {P Q : Piece W ρ.length} (hPl : P.coordinate = j) (hQl : Q.coordinate = i)
    {b' a' pT pS oT oS : ℕ} (hb' : b' = (hx.imagePiece P).start + pT)
        (ha' : a' = (hx.imagePiece Q).start + pS)
    (hpT : pT + ρ.length ≤ retainedLength (N := N) (x := x) P)
    (hpS : pS + ρ.length ≤ retainedLength (N := N) (x := x) Q) (hoT : oT ≤ P.len) (hoS : oS ≤ Q.len)
    (hT : SameStatePhase N ρ.length oT pT) (hS : SameStatePhase N ρ.length oS pS)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a')
    (hlen : P.len - oT ≤ Q.len - oS)
    (hfol : P.stop = (W j).length ∨ (P.len - oT = Q.len - oS ∧ SuffixComparison (W j) P.stop
        (W i) Q.stop)) :
    SuffixComparison (W j) (P.start + oT) (W i) (Q.start + oS) ∧ T.runPrefix W j (P.start + oT) =
        T.runPrefix (editedTuple W ρ N x) j b' ∧
      T.runPrefix W i (Q.start + oS) = T.runPrefix (editedTuple W ρ N x) i a' := by sorry
