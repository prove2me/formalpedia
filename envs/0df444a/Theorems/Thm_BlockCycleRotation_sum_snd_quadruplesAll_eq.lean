-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_snd_quadruplesAll_eq
-- name    : BlockCycleRotation.sum_snd_quadruplesAll_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:58.273355+00:00
-- url     : https://prove2.me/theorems/cac4e343-2672-467a-89ce-fe9347fe32a4
-- title:
--   The `b`-elimination for the coprime quadruples
-- statement:
--   The `b`-elimination for the coprime quadruples.
--
--   In Blomer–Bux this is **§4**, “Coprime `b`-elimination”. It is used in the proof of `Q_eq_tripleSum`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L173-L212

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_snd_quadruplesAll_eq {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesAll n, q.2.1
      = ∑ t ∈ coprimeTriples n, (n - t.2.1 * t.2.2) / t.1 := by sorry
