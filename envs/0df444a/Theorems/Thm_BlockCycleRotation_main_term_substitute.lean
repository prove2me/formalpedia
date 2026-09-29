-- Prove2me | Theorems.Thm_BlockCycleRotation_main_term_substitute
-- name    : BlockCycleRotation.main_term_substitute
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:42.010681+00:00
-- url     : https://prove2.me/theorems/bef0f926-405c-4472-abcb-b00a6dc40fc4
-- title:
--   The substitution
-- statement:
--   **The substitution.** The main term at a coprime pair is `d·m/(a+a') + m²·cTerm(a,a')`.
--
--   In Blomer–Bux this is **Lemma 19**, “Substitution: `C` appears”. It is used in the proofs of `G1term_eq`, `bulk_pair_estimate`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L292-L308

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.main_term_substitute {m d a a' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a)
    (h3 : Nat.gcd a a' = 1) :
    (1 / (a : ℝ)) * ((((d * a : ℕ) : ℝ) + (m : ℝ) / (a : ℝ)) * ((m : ℝ) / ((a : ℝ) + (a' : ℝ)))
        + (-(a' : ℝ) / (a : ℝ)) * ((m : ℝ) / ((a : ℝ) + (a' : ℝ))) ^ 2 / 2)
      = (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a') := by sorry
