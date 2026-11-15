-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussianReal_expectation_narrow_limit
-- name    : AppliedSDE.SarkkaSolin.gaussianReal_expectation_narrow_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:55:43.845148+00:00
-- url     : https://prove2.me/theorems/c050c09d-fba6-4fce-9645-3b7e9e91265e
-- title:
--   Gaussian measures with vanishing variance converge to a point mass in bounded continuous expectation
-- statement:
--   For bounded continuous f, when h decreases to zero from the right, the Gaussian law with mean y+b*h and variance (q*h).toNNReal converges in expectation of f to f(y). This states narrow convergence of Gaussian distributions to the Dirac mass. It is a reusable, distinctly measure-theoretic child of the Gaussian transition-density initial condition theorem 45882bf3-274d-457a-b807-a8c188685a8d.
-- source:
--   Sarkka and Solin (2019), Gaussian Fokker Planck initial condition; supports 45882bf3-274d-457a-b807-a8c188685a8d and Gaussian integral-law theorem df2b7e83-6133-4c73-9f18-3eff0b64c60a.

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.gaussianReal_expectation_narrow_limit
    (b q y : ℝ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hfb : ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) :
    Tendsto
      (fun h : ℝ =>
        ∫ x : ℝ, f x ∂(gaussianReal (y + b * h) (q * h).toNNReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  sorry
