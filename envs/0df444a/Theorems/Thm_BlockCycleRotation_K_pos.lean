-- Prove2me | Theorems.Thm_BlockCycleRotation_K_pos
-- name    : BlockCycleRotation.K_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:57.298085+00:00
-- url     : https://prove2.me/theorems/1fd23a2f-af39-4b3b-b6e1-b99d3762fe7d
-- title:
--   Continuants of lists of positive entries are positive
-- statement:
--   Continuants of lists of positive entries are positive.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proofs of `K_dropLast_lt`, `cf_K`, `quadExpansion_shift`, `shift_expansion_bijection`, and 1 further result(s).
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L112-L124

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.K_pos : ∀ l : List ℕ, (∀ c ∈ l, 1 ≤ c) → 1 ≤ K l := by sorry
