-- Prove2me | Theorems.Thm_BlockCycleRotation_K_reverse
-- name    : BlockCycleRotation.K_reverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:43.115716+00:00
-- url     : https://prove2.me/theorems/10840b64-14d9-48d4-85b7-5ace00fa4ac6
-- title:
--   Continuants are palindromic
-- statement:
--   **Continuants are palindromic**: `K` is invariant under reversing the list. This is what lets Heilbronn's bijection read the second half of the expansion backwards.
--
--   In Blomer–Bux this is **Heilbronn 1969**, “Continuants are palindromic”. It is used in the proofs of `K_tail_lt`, `heilbronn_split_roundtrip`, `heilbronn_surjective`, `quadExpansion_spec`, and 1 further result(s).
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Heilbronn 1969. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L75-L89

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.K_reverse : ∀ l : List ℕ, K l.reverse = K l := by sorry
