-- Prove2me | Theorems.Thm_AvramDividend_Classical_sup_image_sub_const_eq
-- name    : AvramDividend.Classical.sup_image_sub_const_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:28:10.257527+00:00
-- url     : https://prove2.me/theorems/0693f4e2-2ee4-47a5-a549-016d25b4addc
-- title:
--   Subtracting a constant from a bounded nonempty real set shifts its supremum
-- statement:
--   For every nonempty real set S bounded above and constant c, the supremum of its image under z↦z−c equals sup(S)−c. This elementary order-translation identity connects the shifted running supremum in the dividend strong-Markov calculation with the accepted post-upcrossing record increment.

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Tactic.Linarith

open Set

theorem AvramDividend.Classical.sup_image_sub_const_eq
    (S : Set ℝ) (c : ℝ) (hne : S.Nonempty) (hb : BddAbove S) :
    sSup ((fun z : ℝ => z - c) '' S) = sSup S - c := by sorry
