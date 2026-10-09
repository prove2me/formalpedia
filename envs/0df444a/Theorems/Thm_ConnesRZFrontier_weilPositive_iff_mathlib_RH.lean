-- Prove2me | Theorems.Thm_ConnesRZFrontier_weilPositive_iff_mathlib_RH
-- name    : ConnesRZFrontier.weilPositive_iff_mathlib_RH
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T16:48:57.846517+00:00
-- url     : https://prove2.me/theorems/22770c57-ee68-4a0c-96e7-e0ef164a79f9
-- title:
--   Global Connes Weil positivity is equivalent to Mathlib RH
-- statement:
--   For the unchanged Connes arithmetic Weil distribution, global Weil positivity is equivalent to Mathlib’s Riemann hypothesis. Positivity means: for every smooth compactly supported complex-valued function g on the real line, the real part of W(g convolved with starInv(g)) is nonnegative. Mathlib RH means every zero of its Riemann zeta function other than a negative even integer and the point 1 has real part 1/2. The equivalence uses the already certified two directions of the Weil criterion and the certified equivalence between the critical-strip and global RH formulations. Neither Weil positivity nor RH is asserted unconditionally.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/RHSpine.lean, ConnesRZFrontier.weilPositive_iff_mathlib_RH at native compiling commit e348db588b5acb95a2bf9bf73bc9a10890c3f92e; public signature unfolds the unchanged native WeilPositive predicate. Independent proof assembles the two already certified native Weil-criterion directions with the RH-scope bridge.

import Definitions.Def_ConnesRZ_weil_defs
import Mathlib.NumberTheory.LSeries.Nonvanishing
set_option autoImplicit false
open Complex

theorem ConnesRZFrontier.weilPositive_iff_mathlib_RH :
    (∀ g : ℝ → ℂ, ConnesRZ.IsTest g →
      0 ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv g (ConnesRZ.starInv g))).re) ↔
    RiemannHypothesis := by sorry
