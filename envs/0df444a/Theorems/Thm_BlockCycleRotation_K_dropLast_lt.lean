-- Prove2me | Theorems.Thm_BlockCycleRotation_K_dropLast_lt
-- name    : BlockCycleRotation.K_dropLast_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:43.475793+00:00
-- url     : https://prove2.me/theorems/8380ca03-5a7b-498d-975f-d36c17a111a1
-- title:
--   Dropping the last entry strictly decreases the continuant, provided at least two entries remain in play
-- statement:
--   Dropping the last entry strictly decreases the continuant, provided at least two entries remain in play.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proofs of `K_dropLast_lt_prime`, `K_tail_lt`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L126-L145

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.K_dropLast_lt : ∀ l : List ℕ, 2 ≤ l.length → (∀ c ∈ l, 1 ≤ c) →
    K l.dropLast < K l := by sorry
