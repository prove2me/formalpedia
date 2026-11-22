-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_deep
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.site_deep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:10.698699+00:00
-- url     : https://prove2.me/theorems/341f4770-78b1-48aa-91db-1e1ed18a24d7
-- title:
--   Admissible Deletion: site deep
-- statement:
--   A deleted position lies in the site of every piece of its word that contains it (sites
--   are deep inside their pieces, and distinct pieces overlap in fewer than `d` letters).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L226-L242
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L226-L242

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
variable (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ)
variable {W ρ N x}

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.site_deep (hx : AdmissibleDeletion W ρ N x) {l : Fin k} {p : ℕ}
    (hp : p ∈ deletedPositions W ρ N x l) (Q : Piece W ρ.length) (hQl : Q.coordinate = l)
        (hQ1 : Q.start ≤ p)
    (hQ2 : p < Q.stop) : Q ∈ piecesOf W ρ ∧ x Q ≠ 0 ∧ Q.start + Periodic.boundaryMargin N ρ.length ≤
        p ∧
      p < Q.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length *
          x Q := by sorry
