-- Prove2me | Theorems.Thm_BlockCycleRotation_heilbronn_split_roundtrip
-- name    : BlockCycleRotation.heilbronn_split_roundtrip
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:55.748789+00:00
-- url     : https://prove2.me/theorems/0c69975f-a875-421f-8c73-ca703eda6e9d
-- title:
--   The round trip on a split
-- statement:
--   **The round trip on a split.** For a normalised expansion `L` and an interior split point, both halves are recovered from their continuants — the prefix directly, the suffix after reversing. This is what makes the passage from splits to quadruples injective.
--
--   In Blomer–Bux this is **§4**, “Round trip on a split”. It is used in the proof of `sum_split_eq_sum_quadruples`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L668-L714

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.heilbronn_split_roundtrip {L : List ℕ} (hpos : ∀ c ∈ L, 1 ≤ c)
    (hhead : ∀ x ∈ L.head?, 2 ≤ x) (hlast : ∀ x ∈ L.getLast?, 2 ≤ x)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j < L.length) :
    cf (K (L.take j)) (K (L.take j).dropLast) = L.take j
      ∧ cf (K (L.drop j)) (K (L.drop j).tail) = (L.drop j).reverse := by sorry
