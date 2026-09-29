-- Prove2me | Theorems.Thm_BlockCycleRotation_cf_K
-- name    : BlockCycleRotation.cf_K
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:15.639704+00:00
-- url     : https://prove2.me/theorems/5c2bb998-ec6d-47d9-b2a2-9d868d251cdb
-- title:
--   Heilbronn's correspondence, injectivity
-- statement:
--   **Heilbronn's correspondence, injectivity.** A normalised expansion is recovered from its pair of continuants. Normalisation is `2 ≤ c₀`: without it `[1, c]` and `[c+1]` have the same pair, which is the familiar ambiguity of continued fractions.
--
--   In Blomer–Bux this is **Heilbronn 1969**, “Heilbronn, injectivity”. It is used in the proofs of `heilbronn_bijection`, `heilbronn_split_roundtrip`, `quadExpansion_shift`, `shift_expansion_bijection`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Heilbronn 1969. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L290-L335

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cf_K : ∀ l : List ℕ, l ≠ [] → (∀ c ∈ l, 1 ≤ c) → (∀ x ∈ l.head?, 2 ≤ x) →
    cf (K l) (K l.dropLast) = l := by sorry
