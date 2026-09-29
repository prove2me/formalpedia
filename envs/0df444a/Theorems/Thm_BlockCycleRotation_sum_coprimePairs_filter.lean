-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_coprimePairs_filter
-- name    : BlockCycleRotation.sum_coprimePairs_filter
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:09.066166+00:00
-- url     : https://prove2.me/theorems/27201674-b088-447d-9763-d8b17239e5af
-- title:
--   The pairs, decomposed by their first component
-- statement:
--   The pairs, decomposed by their first component.
--
--   In Blomer–Bux this is **§4**, “Pairs decomposed by first component”. It is used in the proofs of `lower_order_le`, `middle_layer_bound`, `small_part_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L943-L967

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_coprimePairs_filter {M : Type*} [AddCommMonoid M] {m d : ℕ} (g : ℕ → ℕ → M) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m), g p.1 p.2
      = ∑ a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
          ∑ a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1), g a a' := by sorry
