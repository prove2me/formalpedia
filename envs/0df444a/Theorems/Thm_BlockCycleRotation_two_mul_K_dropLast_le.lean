-- Prove2me | Theorems.Thm_BlockCycleRotation_two_mul_K_dropLast_le
-- name    : BlockCycleRotation.two_mul_K_dropLast_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:36.125833+00:00
-- url     : https://prove2.me/theorems/86b73016-e827-4071-8dc6-3309070c117f
-- title:
--   Conversely, an expansion whose last entry is at least `2` has `2 · K L
-- statement:
--   Conversely, an expansion whose last entry is at least `2` has `2 · K L.dropLast ≤ K L`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proofs of `quadExpansion_shift`, `shift_expansion_bijection`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L500-L520

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.two_mul_K_dropLast_le : ∀ L : List ℕ, L ≠ [] → (∀ c ∈ L, 1 ≤ c) →
    (∀ x ∈ L.getLast?, 2 ≤ x) → 2 * K L.dropLast ≤ K L := by sorry
