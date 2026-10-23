-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_compensated_kernel_joint_measurable
-- name    : AvramDividend.Classical.chat07_bv_compensated_kernel_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:29:11.134432+00:00
-- url     : https://prove2.me/theorems/ad9c7e01-7df1-48d9-a3ce-3318dbe6041b
-- title:
--   Joint measurability of the truncated compensated negative-jump scale kernel
-- statement:
--   For any monotone real-valued scale candidate W and real exponential weighting parameter theta, the two-variable function of positive reserve and jump magnitude defining the absolutely weighted generator jump kernel with the unit compensation truncation is Borel measurable. This follows from measurable monotone functions, the theorem that ordinary derivatives are measurable even without global C1 regularity, and stability of measurability under arithmetic and measurable case distinctions.

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FunProp

open MeasureTheory

theorem AvramDividend.Classical.chat07_bv_compensated_kernel_joint_measurable
    (W : ℝ → ℝ) (hW : Monotone W) (θ : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        |W (p.1 - p.2) - W p.1 +
          (if p.2 < 1 then p.2 * deriv W p.1 else 0)|) := by sorry
