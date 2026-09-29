-- Prove2me | Theorems.Thm_BlockCycleRotation_G1term_eq
-- name    : BlockCycleRotation.G1term_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:04.410085+00:00
-- url     : https://prove2.me/theorems/ef328a1a-566b-4c43-b2a4-1a93584e2811
-- title:
--   `G₁` is the summand of `G₁(n)`, by `main_term_substitute`
-- statement:
--   `G₁` is the summand of `G₁(n)`, by `main_term_substitute`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L217-L222

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Theorem13
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.G1term_eq {m d a a' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a) (h3 : Nat.gcd a a' = 1) :
    G1term m d a a'
      = (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a') := by sorry
