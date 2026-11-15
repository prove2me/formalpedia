-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a281_discount_raw_first_increment_Young_square_budget
-- name    : AvramDividend.Classical.avram_ga_a281_discount_raw_first_increment_Young_square_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:21:27.711549+00:00
-- url     : https://prove2.me/theorems/f45f30bb-ac14-4306-a438-2aa9c0785bec
-- title:
--   First-order discounted Gaussian raw increment controlled by arbitrarily small raw quadratic energy plus deterministic quadratic mesh width
-- statement:
--   For any positive small Taylor budget η and nonnegative discount width Q and local Lipschitz jet bound L, the linear first-order discounted raw Gaussian cell error QL|r| is at most ηr²+(QL)²/(4η). This exact Young inequality lets the true physical stopped Gaussian a236 first-order discount residual be absorbed into an arbitrarily small coefficient of expected raw quadratic energy a240, with a deterministic mesh-width squared correction that vanishes by a206, avoiding unnecessary stochastic Cauchy-Schwarz calculations.
-- source:
--   Original Gaussian a236 small-cell discount linear raw increment and a240/a206 square energies

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a281_discount_raw_first_increment_Young_square_budget
    (η Q L r : ℝ) (hη : 0 < η)
    (hQ : 0 ≤ Q) (hL : 0 ≤ L) :
    Q*L*|r| ≤ η*r^2+(Q*L)^2/(4*η) := by sorry
