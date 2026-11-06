-- Prove2me | Theorems.Thm_BianchiIX_terminal_amplitude_power_budget
-- name    : BianchiIX.terminal_amplitude_power_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:51:08.823842+00:00
-- url     : https://prove2.me/theorems/30f38754-aba9-4115-ab36-c0b0491f9fd8
-- title:
--   Terminal products retain the amplitude exponent nineteen tenths
-- statement:
--   Suppose $0<\alpha\leq1$, $0<b\leq\alpha^{40}$, $A\geq1$,
--   $U,W\geq0$, $U+W\leq b$, and
--   $$0\leq u\leq\alpha^4,\quad 0\leq v\leq AW/\alpha^2,
--   \quad0\leq w\leq AU/\alpha^2.$$
--   Then
--   $$uv^{19/10}\leq A^2b^{19/10},\qquad wv\leq A^2b^{19/10}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/TerminalAmplitudePowers.lean#L12-L60

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.terminal_amplitude_power_budget {α b A U W u v w : ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hb : 0 < b) (hbudget : b ≤ α ^ (40 : ℕ)) (hA : 1 ≤ A)
    (hU : 0 ≤ U) (hW : 0 ≤ W) (hsum : U + W ≤ b)
    (hu : 0 ≤ u ∧ u ≤ α ^ (4 : ℕ)) (hv : 0 ≤ v ∧ v ≤ A * W / α ^ 2)
    (hw : 0 ≤ w ∧ w ≤ A * U / α ^ 2) :
    u * v ^ (19 / 10 : ℝ) ≤ A ^ 2 * b ^ (19 / 10 : ℝ) ∧
      w * v ≤ A ^ 2 * b ^ (19 / 10 : ℝ) := by sorry
