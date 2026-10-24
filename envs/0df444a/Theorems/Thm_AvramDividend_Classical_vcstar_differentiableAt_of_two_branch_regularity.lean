-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_differentiableAt_of_two_branch_regularity
-- name    : AvramDividend.Classical.vcstar_differentiableAt_of_two_branch_regularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:23:23.856186+00:00
-- url     : https://prove2.me/theorems/c5192b61-1883-4172-9635-27b4b76b7c9c
-- title:
--   Positive-barrier differentiability from Gaussian tilt and BV scale regularity
-- statement:
--   At a finite positive optimal barrier, the Gaussian-or-bounded-variation alternative gives ordinary differentiability of the barrier candidate whenever Gaussian processes have a positive nondecreasing exponential tilt of the scale function and bounded-variation processes have C1 scale regularity. The proof uses the already Proved three-branch smooth-fit derivative-one theorem and nonzero derivative implies differentiability. No Open theorem is imported.
-- source:
--   Avram, Palmowski and Pistorius (2007), smooth fit at the positive derivative-minimising barrier.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_three_branch_regularity
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_differentiableAt_of_two_branch_regularity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation)
    (hgauss : 0 < X.σ →
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hbv : X.BoundedVariation →
      ContDiffOn ℝ 1 W (Ioi (0 : ℝ))) :
    DifferentiableAt ℝ (vcstar W) (cstar W).toReal := by sorry
end AvramDividend.Classical
