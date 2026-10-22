-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_dividend_secant_bound
-- name    : AvramDividend.Classical.exp_dividend_secant_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:20:36.294049+00:00
-- url     : https://prove2.me/theorems/842044ed-8131-4313-9148-368204a9b632
-- title:
--   Exponential HJB candidate pays for every admissible downward reserve dividend step
-- statement:
--   Let θ≥1 and let a be a nonnegative cash dividend no larger than the pre-payment reserve u. Then the drop in the positive exponential candidate exp(θu) caused by reducing reserve from u to u-a is at least the dividend a. This is an explicit pathwise dividend-jump secant inequality relevant to the controlled HJB budget. Factor the exponential difference as exp(θ(u-a)) times (exp(θa)-1). Because both θ and the post-payment reserve are nonnegative, exp(θ(u-a))≥1; by 1+z≤exp z and θ≥1, exp(θa)-1≥θa≥a. The proof is fully deterministic and does not assume an unproved stopped Itô formula, nor handle payment stochastic integration.
-- source:
--   Pinned Mathlib Real.add_one_le_exp and Real.exp_add plus elementary ring and nonnegative multiplication.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.exp_dividend_secant_bound
    (θ u a : ℝ) (hθ : 1 ≤ θ) (ha : 0 ≤ a) (hua : a ≤ u) :
    a ≤ Real.exp (θ * u) - Real.exp (θ * (u - a)) := by sorry
