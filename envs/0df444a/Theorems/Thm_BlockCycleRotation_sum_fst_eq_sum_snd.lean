-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_fst_eq_sum_snd
-- name    : BlockCycleRotation.sum_fst_eq_sum_snd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:07.050343+00:00
-- url     : https://prove2.me/theorems/cf8bc7d9-2ebc-4677-83dc-997a81a85c53
-- title:
--   Summing `a` over the quadruples is the same as summing `b`
-- statement:
--   **Summing `a` over the quadruples is the same as summing `b`.** The paper uses this to symmetrise; it is the involution swapping the two halves of the quadruple.
--
--   In Blomer–Bux this is **§4**, “Quadruples symmetric, `∑a = ∑b`”. It is used in the proof of `heilbron`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L895-L913

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_fst_eq_sum_snd (n : ℕ) :
    ∑ q ∈ quadruples n, q.1 = ∑ q ∈ quadruples n, q.2.1 := by sorry
