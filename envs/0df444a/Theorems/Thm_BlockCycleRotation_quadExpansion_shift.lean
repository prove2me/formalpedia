-- Prove2me | Theorems.Thm_BlockCycleRotation_quadExpansion_shift
-- name    : BlockCycleRotation.quadExpansion_shift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:03.319481+00:00
-- url     : https://prove2.me/theorems/d58b28fb-0e25-4e4e-9982-8db40c09f5a7
-- title:
--   The shift attached to a quadruple lies in `shifts n`, and its expansion is the reassembled one
-- statement:
--   The shift attached to a quadruple lies in `shifts n`, and its expansion is the reassembled one.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `sum_split_eq_sum_quadruples`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L808-L825

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.quadExpansion_shift {n a b a' b' : ℕ} (hq : (a, b, a', b') ∈ quadruples n) :
    K (quadExpansion a b a' b').dropLast ∈ shifts n
      ∧ cf n (K (quadExpansion a b a' b').dropLast) = quadExpansion a b a' b' := by sorry
