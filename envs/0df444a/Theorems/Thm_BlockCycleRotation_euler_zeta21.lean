-- Prove2me | Theorems.Thm_BlockCycleRotation_euler_zeta21
-- name    : BlockCycleRotation.euler_zeta21
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:34.198684+00:00
-- url     : https://prove2.me/theorems/47a2bfd6-b224-4807-920d-82125387b435
-- title:
--   Euler's $\zeta(2,1) = \zeta(3)$
-- statement:
--   The multiple zeta value $\zeta(2,1) = \sum_{m>n\ge 1} m^{-2} n^{-1}$ equals $\zeta(3)$.
--
--   Euler's classical evaluation, cited in Remark 21 and proved here by telescoping the partial sums against the harmonic numbers. It is the ingredient that turns the alternative form of $C$ into something that can be enclosed numerically.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 21 (cited). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L647-L665

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.euler_zeta21 : zeta21 = zeta3 := by sorry
