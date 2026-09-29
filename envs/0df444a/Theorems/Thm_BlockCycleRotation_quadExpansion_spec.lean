-- Prove2me | Theorems.Thm_BlockCycleRotation_quadExpansion_spec
-- name    : BlockCycleRotation.quadExpansion_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:56.67405+00:00
-- url     : https://prove2.me/theorems/411a5360-37f0-48fe-b0c0-dbae4d4c4aa2
-- title:
--   The expansion attached to a quadruple is the split it came from
-- statement:
--   **The expansion attached to a quadruple is the split it came from.** It is a normalised expansion of `n`, and splitting it at `|cf a a'|` returns the two halves.
--
--   In Blomer–Bux this is **§4**, “Expansion attached to a quadruple”. It is used in the proofs of `quadExpansion_shift`, `sum_split_eq_sum_quadruples`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L768-L806

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.quadExpansion_spec {n a b a' b' : ℕ} (hq : (a, b, a', b') ∈ quadruples n) :
    K (quadExpansion a b a' b') = n ∧ quadExpansion a b a' b' ≠ []
      ∧ (∀ c ∈ quadExpansion a b a' b', 1 ≤ c)
      ∧ (∀ x ∈ (quadExpansion a b a' b').head?, 2 ≤ x)
      ∧ (∀ x ∈ (quadExpansion a b a' b').getLast?, 2 ≤ x)
      ∧ (quadExpansion a b a' b').take (cf a a').length = cf a a'
      ∧ (quadExpansion a b a' b').drop (cf a a').length = (cf b b').reverse
      ∧ 1 ≤ (cf a a').length
      ∧ (cf a a').length < (quadExpansion a b a' b').length := by sorry
