-- Prove2me | Theorems.Thm_BlockCycleRotation_tsum_gTerm_ge
-- name    : BlockCycleRotation.tsum_gTerm_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:30.810785+00:00
-- url     : https://prove2.me/theorems/bb5ead9d-0406-492e-8eb3-6e663b07297e
-- title:
--   tsum gTerm ge
-- statement:
--   A supporting lemma of the formalization, declared as `tsum_gTerm_ge`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L596-L640

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

set_option maxHeartbeats 800000 in
-- Several tsum manipulations chained.

theorem BlockCycleRotation.tsum_gTerm_ge :
    (∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a')) + (54 / 100) * (1 / 61)
      ≤ ∑' p, gTerm p := by sorry
