-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_exists_piece_of_stretch
-- name    : DeciSigma1.Holes.Periodic.exists_piece_of_stretch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:32.922355+00:00
-- url     : https://prove2.me/theorems/a5e1b919-2246-4538-81af-0695eced3972
-- title:
--   Periodic: exists piece of stretch
-- statement:
--   A periodic stretch of length `≥ 2d` with a primitive window lies in a piece; a left
--   (right) break at the stretch fixes the piece start (end).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L321-L383
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L321-L383

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

theorem DeciSigma1.Holes.Periodic.exists_piece_of_stretch (W : Fin k → List α) (l : Fin k) {d x y : ℕ}
    (hxy : x + 2 * d ≤ y) (hy : y ≤ (W l).length) (hper : PeriodicOn (W l) d x y)
    (hprim : IsPrimitive (((W l).drop x).take d)) :
    ∃ P : Piece W d, P.coordinate = l ∧ P.start ≤ x ∧ y ≤ P.stop ∧
      IsConjugate P.root (((W l).drop x).take d) ∧
      ((x = 0 ∨ (W l)[x - 1]? ≠ (W l)[x - 1 + d]?) → P.start = x) ∧
      ((y = (W l).length ∨ (W l)[y]? ≠ (W l)[y - d]?) → P.stop = y) := by sorry
