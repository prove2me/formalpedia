-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_piece_suffixComparison
-- name    : DeciSigma1.Holes.Periodic.piece_suffixComparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:44:31.475412+00:00
-- url     : https://prove2.me/theorems/30f45c45-c2c4-4b73-bb0a-90a933a98419
-- title:
--   Periodic: piece suffix Comparison
-- statement:
--   Two pieces whose texts agree on `d` letters from the offsets `oP`, `oQ` compare from those
--   offsets, provided the host piece has at least as much room and either the target piece ends its
--   word or the rooms are equal and the followers compare.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L260-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L260-L285

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
variable [DecidableEq α] {W : Fin k → List α} {d : ℕ}
omit [DecidableEq α]

theorem DeciSigma1.Holes.Periodic.piece_suffixComparison (P Q : Piece W d) {oP oQ : ℕ} (hoP : oP ≤ P.len) (hoQ : oQ ≤ Q.len)
    (hanchor : ∀ t < d,
        t < P.len - oP → (W P.coordinate)[P.start + oP + t]? = (W Q.coordinate)[Q.start + oQ + t]?)
    (hlen : P.len - oP ≤ Q.len - oQ)
    (hfol : P.stop = (W P.coordinate).length ∨ (P.len - oP = Q.len - oQ ∧ SuffixComparison
        (W P.coordinate) P.stop (W Q.coordinate) Q.stop)) :
    SuffixComparison (W P.coordinate) (P.start + oP) (W Q.coordinate) (Q.start + oQ) := by sorry
