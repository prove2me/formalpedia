-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_copy_piece
-- name    : DeciSigma1.Holes.Periodic.copy_piece
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:44:21.645173+00:00
-- url     : https://prove2.me/theorems/907823ce-ce0e-4917-b03e-84e833545252
-- title:
--   Periodic: copy piece
-- statement:
--   A piece whose start (with its left break) lies inside a stretch where two words agree is
--   copied: the other word has a piece starting at the corresponding cut with the same root, at
--   least as long as the copied part, and ending at the corresponding cut when its right break is
--   copied too.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L109-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L109-L193

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
variable [DecidableEq α] {V : Fin k → List α} {d : ℕ}
omit [DecidableEq α]

theorem DeciSigma1.Holes.Periodic.copy_piece {a b : Fin k} {u v m : ℕ}
    (hag : ∀ n < m, (V a)[u + n]? = (V b)[v + n]?) (R : Piece V d) (hRl : R.coordinate = a)
    (h1 : u < R.start) {ℓ : ℕ} (hℓ : 2 * d ≤ ℓ) (hℓR : R.start + ℓ ≤ R.stop)
        (hℓm : R.start + ℓ ≤ u + m) :
    ∃ P : Piece V d, P.coordinate = b ∧ P.start = v + (R.start - u) ∧ P.root = R.root ∧
      v + (R.start - u) + ℓ ≤ P.stop ∧
      (R.stop < u + m → R.stop < (V a).length → P.stop = v + (R.stop - u)) := by sorry
