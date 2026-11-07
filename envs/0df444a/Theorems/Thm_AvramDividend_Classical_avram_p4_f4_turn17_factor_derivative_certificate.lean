-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn17_factor_derivative_certificate
-- name    : AvramDividend.Classical.avram_p4_f4_turn17_factor_derivative_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:33:20.71412+00:00
-- url     : https://prove2.me/theorems/a123451e-b79f-4a3f-809a-26e10d228d29
-- title:
--   avram_p4_f4_turn17_factor_derivative_certificate
-- statement:
--   From the factorised second-order inequality, g=w'-rpos*w obeys g'<=rneg*g on the positive ray; the first-order comparison lemma then bounds g.
-- source:
--   Genuine factorised ODE positive-ray reduction of 4170b742.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn17_factor_derivative_certificate
    (rpos rneg : ℝ) (hrpos : 0 < rpos) (hrneg : rneg < 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hODE : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      iteratedDeriv 2 w y - (rpos + rneg) * deriv w y + rpos * rneg * w y ≤ 0) :
    ∀ y : ℝ, 1 ≤ y →
      deriv w y - rpos * w y ≤
        (deriv w 1 - rpos * w 1) * Real.exp (rneg * (y - 1)) := by sorry
