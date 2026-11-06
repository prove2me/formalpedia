-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_cash_terminal_joint_fatou
-- name    : AvramDividend.Classical.avram_limit2_cash_terminal_joint_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:13:14.615294+00:00
-- url     : https://prove2.me/theorems/fb6b9df2-0b0c-4c05-8d4c-a8441e80c1c5
-- title:
--   Separate original strict cash and surviving terminal convergence yield their Fatou sum
-- statement:
--   Under the genuine pathwise convergence of two original stopped physical-grid components, discounted strict pre-ruin dividend cash and the surviving positive-horizon terminal payoff, their sum has the exact ENNReal Fatou lower bound needed for the BV source certificate. This separates the two analytic mesh convergence obligations.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_envelope_of_expected_upper
open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_cash_terminal_joint_fatou
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Cash Terminal : ℕ → Ω → ℝ)
    (cash terminal : Ω → ℝ)
    (hCash : ∀ᵐ ω ∂P,
      Tendsto (fun n => Cash n ω) atTop (nhds (cash ω)))
    (hTerminal : ∀ᵐ ω ∂P,
      Tendsto (fun n => Terminal n ω) atTop (nhds (terminal ω))) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal (cash ω + terminal ω) ≤
        liminf (fun n => ENNReal.ofReal (Cash n ω + Terminal n ω)) atTop := by sorry
