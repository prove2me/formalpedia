-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_linear_covariance_lyapunov
-- name    : AppliedSDE.SarkkaSolin.stationary_linear_covariance_lyapunov
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:55:23.283787+00:00
-- url     : https://prove2.me/theorems/a1a137e9-94d8-4ec8-b046-0049726c0d8b
-- title:
--   Stationary linear-SDE covariance solves the continuous Lyapunov equation
-- statement:
--   Original derived from Chapter 6.5, equations for linear SDE covariance propagation and stationary Lyapunov equilibrium. Let P(t) be a differentiable matrix-valued covariance trajectory satisfying P′=FP+PFᵀ+Q for a constant drift matrix F and noise covariance Q. If P is stationary with value P∞, prove FP∞+P∞Fᵀ+Q=0. This is the full finite-dimensional algebraic Lyapunov condition, conditional on the covariance evolution law. The stochastic derivation of that evolution and existence and uniqueness of a stable stationary covariance remain further obligations.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   FP_\infty+P_\infty F^\top+Q=0
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Section 6.5, covariance propagation and stationary Lyapunov equation, printed pp. 88–91. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped BigOperators Topology

theorem AppliedSDE.SarkkaSolin.stationary_linear_covariance_lyapunov
    (n : ℕ)
    (F Q Pstat : Matrix (Fin n) (Fin n) ℝ)
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hstationary : ∀ t : ℝ, P t = Pstat)
    (hCovODE : ∀ (t : ℝ) (i j : Fin n),
      deriv (fun s : ℝ => P s i j) t =
        (F * P t + P t * F.transpose + Q) i j) :
    F * Pstat + Pstat * F.transpose + Q = 0 := by
  sorry
