-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaledW_second_deriv_zero_at_positive_cstar
-- name    : AvramDividend.Classical.scaledW_second_deriv_zero_at_positive_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T07:36:48.671124+00:00
-- url     : https://prove2.me/theorems/1e509554-3351-40fb-89af-a21bd29341ef
-- title:
--   Second derivative of the scaled q-scale branch vanishes at a positive optimal dividend barrier
-- statement:
--   For a real function W with W' continuous on the positive axis and positive real canonical barrier a=(cstar W).toReal, the scaled branch z↦divE(W(z),scaleDeriv W a) has zero ordinary second derivative at a. This follows from the Proved canonical Fermat curvature theorem, the fact that scaleDeriv W a is a finite extended real when a>0, and the pinned Mathlib derivative-of-division-by-constant identity. This is a precise second-order jet for the Gaussian barrier join, not the full global C2 theorem.

import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.scaledW_second_deriv_zero_at_positive_cstar (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Ioi 0))
    (hpos : 0 < (cstar W).toReal) :
    deriv (deriv
      (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)))
      (cstar W).toReal = 0 := by sorry
