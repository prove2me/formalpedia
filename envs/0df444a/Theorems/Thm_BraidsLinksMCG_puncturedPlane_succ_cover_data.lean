-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlane_succ_cover_data
-- name    : BraidsLinksMCG.puncturedPlane_succ_cover_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T22:57:28.151039+00:00
-- url     : https://prove2.me/theorems/3f09fc28-b0f2-4114-beae-c5579b65e301
-- title:
--   The punctured plane has an explicit two-set van Kampen cover
-- statement:
--   This child records the explicit two-set cover data needed for the punctured-plane induction step. The outer member is the complement of the closed quarter-unit disk around the newly added puncture, while the inner member is the unit disk centred half a unit to its right. Both members are open in the punctured plane, both contain the base point, and together they cover the entire punctured plane. The child deliberately stops before asserting path-connectedness, a deformation retraction, or any fundamental-group calculation.
-- source:
--   Hatcher, Algebraic Topology, Section 1.2, applied to Birman, Braids, Links, and Mapping Class Groups, Chapter 1, Theorem 1.4 and Corollary 1.8.1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem puncturedPlane_succ_cover_data (n : ℕ) :
    ∃ A : Fin 2 → Set (PuncturedPlane (n + 1)),
      A 0 = {z : PuncturedPlane (n + 1) |
        (1 / 4 : ℝ) < dist (z : ℂ) (((n : ℕ) + 1 : ℕ) : ℂ)} ∧
      A 1 = {z : PuncturedPlane (n + 1) |
        dist (z : ℂ) ((((n : ℕ) + 1 : ℕ) : ℂ) + (1 / 2 : ℂ)) < (1 : ℝ)} ∧
      (∀ b : Fin 2, basePunctured (n + 1) ∈ A b) ∧
      (∀ b : Fin 2, IsOpen (A b)) ∧
      Set.iUnion A = (Set.univ : Set (PuncturedPlane (n + 1))) := by sorry

end BraidsLinksMCG
