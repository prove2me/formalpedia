-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_piece_eq_of_overlap
-- name    : DeciSigma1.Holes.Periodic.piece_eq_of_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:23.120495+00:00
-- url     : https://prove2.me/theorems/a2dd1789-e6aa-45c6-8f3a-ce197741fd9a
-- title:
--   Periodic: piece eq of overlap
-- statement:
--   Two pieces of the same period in the same word that overlap in at least `d` letters are
--   equal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L245-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L245-L284

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
variable {W : Fin k → List α} {d : ℕ}

theorem DeciSigma1.Holes.Periodic.piece_eq_of_overlap {P Q : Piece W d} (hl : P.coordinate = Q.coordinate)
    (h₁ : P.start + d ≤ Q.stop)
    (h₂ : Q.start + d ≤ P.stop) : P = Q := by sorry
