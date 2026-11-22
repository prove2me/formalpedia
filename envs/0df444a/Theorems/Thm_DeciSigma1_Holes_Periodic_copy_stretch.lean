-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_copy_stretch
-- name    : DeciSigma1.Holes.Periodic.copy_stretch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:46:30.3158+00:00
-- url     : https://prove2.me/theorems/a3600237-714f-4a19-9d08-2243ed229a16
-- title:
--   Periodic: copy stretch
-- statement:
--   A periodic stretch of length `> 2d` inside a piece, seen through an agreement, lies in a
--   piece of the other word of the same class; if the stretch ends with the piece's right break,
--   copied too, the other piece ends at the corresponding cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L199-L246
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L199-L246

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

theorem DeciSigma1.Holes.Periodic.copy_stretch {a b : Fin k} {u v m : ℕ}
    (hag : ∀ n < m, (V a)[u + n]? = (V b)[v + n]?) (R : Piece V d) (hRl : R.coordinate = a)
    (h1 : R.start ≤ u) {ℓ : ℕ} (hℓ : 2 * d < ℓ) (hℓR : u + ℓ ≤ R.stop) (hℓm : ℓ ≤ m) :
    ∃ P : Piece V d, P.coordinate = b ∧ P.start ≤ v ∧ v + ℓ ≤ P.stop ∧ IsConjugate P.root R.root ∧
      (u + ℓ = R.stop → ℓ < m → R.stop < (V a).length → P.stop = v + ℓ) := by sorry
