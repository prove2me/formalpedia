-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_snd_quadruplesAll
-- name    : BlockCycleRotation.sum_snd_quadruplesAll
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:34.150407+00:00
-- url     : https://prove2.me/theorems/e6d408cb-3546-4d2a-820a-7c412228ea4d
-- title:
--   Classifying the quadruples by `gcd(b,b')`
-- statement:
--   **Classifying the quadruples by `gcd(b,b')`.**
--
--   In Blomer–Bux this is **§4**, “Quadruples classified by `gcd(b,b')`”. It is used in the proof of `heilbron`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L1056-L1123

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_snd_quadruplesAll {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesAll n, q.2.1
      = ∑ e ∈ n.divisors, e * ∑ p ∈ quadruples (n / e), p.2.1 := by sorry
