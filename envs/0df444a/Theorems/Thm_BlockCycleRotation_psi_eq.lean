-- Prove2me | Theorems.Thm_BlockCycleRotation_psi_eq
-- name    : BlockCycleRotation.psi_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:24.73168+00:00
-- url     : https://prove2.me/theorems/6c787ce3-6e27-446b-a1e8-7776fcbe5ef1
-- title:
--   The functional equation
-- statement:
--   **The functional equation.** `ψ(x) = 2x + Out(x)·ψ(In(x))`.
--
--   In Blomer–Bux this is **Eq. (essential-recurrence)**, “Functional equation for `ψ`”. It is used in the proof of `psi_rat`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Eq. (essential-recurrence). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L171-L196

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.psi_eq {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psi x = 2 * x + Outt x * psi (Inn x) := by sorry
