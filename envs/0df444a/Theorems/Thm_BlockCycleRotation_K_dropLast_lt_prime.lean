-- Prove2me | Theorems.Thm_BlockCycleRotation_K_dropLast_lt_prime
-- name    : BlockCycleRotation.K_dropLast_lt_prime
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:05.011977+00:00
-- url     : https://prove2.me/theorems/a3ca5af9-d42c-4876-86d1-c69105aefd98
-- title:
--   `K l
-- statement:
--   `K l.dropLast < K l`, allowing a one-element list provided its entry is at least `2` — which is Heilbronn's condition `2 ≤ c₀`.
--
--   In Blomer–Bux this is **Heilbronn 1969**, “Size conditions `a > a' ≥ 1`”. It is used in the proof of `cf_K`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Heilbronn 1969. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L169-L182

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.K_dropLast_lt_prime {l : List ℕ} (hne : l ≠ []) (hpos : ∀ c ∈ l, 1 ≤ c)
    (hsingle : l.length = 1 → 2 ≤ K l) : K l.dropLast < K l := by sorry
