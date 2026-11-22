-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_bound
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.site_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:19.052793+00:00
-- url     : https://prove2.me/theorems/45089c37-21cb-477d-96d8-23c93438a443
-- title:
--   Admissible Deletion: site bound
-- statement:
--   The deleted positions of a shortened piece lie in its middle: after `boundaryMargin`
--   letters, and at least `5 · boundaryMargin + 2 · statePeriodModulus` letters before its end.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L214-L222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L214-L222

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.site_bound (hx : AdmissibleDeletion W ρ N x) {P : Piece W ρ.length}
    (hP : x P ≠ 0) :
    P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P +
        (5 * Periodic.boundaryMargin N ρ.length +
      2 * Periodic.statePeriodModulus N ρ.length) ≤ P.stop := by sorry
