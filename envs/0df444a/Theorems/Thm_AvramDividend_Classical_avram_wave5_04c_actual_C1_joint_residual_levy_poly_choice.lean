-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:48:06.251331+00:00
-- url     : https://prove2.me/theorems/4b96473d-daec-4ae7-93d6-311b5ff859b4
-- title:
--   One genuine C1 polynomial simultaneously approximates all nonnegative source residuals and all original negative Lévy jumps
-- statement:
--   For each nonnegative remote cutoff M and epsilon>0 and each globally C1 payoff, choose ONE polynomial Q vanishing at t=1 that simultaneously satisfies the sharp weighted-error bound for ALL nonnegative original-process residual magnitudes r and ALL negative original Lévy jump marks y, with the same ε and M. The error is ε times the BV exponential weight plus 2 times the original signed payoff increment ONLY on the remote tail. The sharp payoff-increment tail is integrable by GeneratorIntegrable even when ∫|y|ν is infinite. No process coupling, substitute law, generator assumption, or C2 hypothesis.
-- source:
--   Proved global C1 weighted Bernstein with sharp signed-payoff tail, using a=exp(-(M+1)), b=exp(-M) and exact exponential inversion.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_global_weighted_Bernstein_payoff_tail
set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      (∀ r : ℝ, 0 ≤ r →
        |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
          ε * (1 - Real.exp (-r)) +
            (if M < r then 2 * |w x - w (x - r)| else 0)) ∧
      (∀ y : ℝ, y < 0 →
        |Polynomial.eval (Real.exp y) Q - (w x - w (x + y))| ≤
          ε * (1 - Real.exp y) +
            (if y < -M then 2 * |w x - w (x + y)| else 0)) := by sorry
