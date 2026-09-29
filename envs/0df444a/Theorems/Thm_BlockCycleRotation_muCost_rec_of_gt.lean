-- Prove2me | Theorems.Thm_BlockCycleRotation_muCost_rec_of_gt
-- name    : BlockCycleRotation.muCost_rec_of_gt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:05.272596+00:00
-- url     : https://prove2.me/theorems/d0f67035-4f4e-4710-a358-e1d9c030910c
-- title:
--   muCost rec of gt
-- statement:
--   A supporting lemma of the formalization, declared as `muCost_rec_of_gt`.
--
--   In Blomer–Bux this is **Eq. (def-mu-nu)**, “Eq. (def-mu-nu), both branches”. It is used in the proof of `costB_le_muCost`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Eq. (def-mu-nu). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L485-L508

import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.muCost_rec_of_gt {N l b : ℝ} (hN : 0 < N) (hb : 0 < b) (h : b < l)
    (hl : 2 * l ≤ N) :
    muCost N l b - N
      = 2 * l + (muCost (N * Outt (l / N)) (N * Outt (l / N) * Inn (l / N)) b
          - N * Outt (l / N)) := by sorry
