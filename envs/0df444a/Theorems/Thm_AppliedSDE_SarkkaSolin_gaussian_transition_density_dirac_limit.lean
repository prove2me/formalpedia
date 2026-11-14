-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_transition_density_dirac_limit
-- name    : AppliedSDE.SarkkaSolin.gaussian_transition_density_dirac_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:46:38.56507+00:00
-- url     : https://prove2.me/theorems/45882bf3-274d-457a-b807-a8c188685a8d
-- title:
--   Nonzero-drift Gaussian transition density converges weakly to its initial point
-- statement:
--   Theorem 5.10 and eq (5.43), printed p. 68. For the constant-coefficient scalar SDE with nonzero drift, the Gaussian transition probability concentrates on a Dirac mass at its initial state as the horizon tends down to zero. This verifies the initial-condition aspect of the transition-density FPK theorem and explicitly remains a specialisation of general diffusions.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \lim_{t\downarrow0}\int_{\mathbb R}f(x)p_t(x\mid x_0)\,\mathrm dx=f(x_0)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 5.10, equation (5.43), Gaussian transition limiting case, printed p. 68. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped Topology

theorem AppliedSDE.SarkkaSolin.gaussian_transition_density_dirac_limit
    (b q y s : ℝ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hfb : ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) :
    let p : ℝ → ℝ → ℝ := fun x t =>
      Real.exp (-((x - y - b * (t - s)) ^ 2 / (2 * q * (t - s)))) /
        Real.sqrt (2 * Real.pi * q * (t - s));
    Tendsto (fun h : ℝ => ∫ x : ℝ, p x (s + h) * f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  sorry
