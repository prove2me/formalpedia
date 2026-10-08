-- Prove2me | Theorems.Thm_Erdos970_log_of_analytic
-- name    : Erdos970.log_of_analytic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:11:57.068197+00:00
-- url     : https://prove2.me/theorems/18b74c8b-3ad9-4193-a8b4-e48323ea9ba0
-- title:
--   A holomorphic logarithm of a nonvanishing analytic function on a smaller disc
-- statement:
--   Let $0<r_1<R'<R<1$, and let $B:\mathbb C\to\mathbb C$ be analytic on a neighbourhood of every point of the closed disc $|z|\le R$ and nonzero on the closed disc $|z|\le R'$. Then there is $J:\mathbb C\to\mathbb C$, analytic on a neighbourhood of every point of the closed disc $|z|\le r_1$, with $J(0)=0$, such that for every $z$ with $|z|\le r_1$
--
--   $$J'(z)=\frac{B'(z)}{B(z)}\qquad\text{and}\qquad \log|B(z)|-\log|B(0)|=\operatorname{Re}J(z).$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `Erdos970.log_of_analytic`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace Erdos970

open _root_.Complex
open _root_.MeasureTheory
open _root_.intervalIntegral
open scoped Interval
open _root_.Filter
open Topology
open Classical
open scoped Topology

theorem log_of_analytic
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.closedBall (0 : ℂ) r1) ∧
      J_B 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1,
        Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J_B z)) := by
  sorry

end Erdos970
