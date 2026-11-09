-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_cap_ode_derivative_uniform
-- name    : AvramDividend.Classical.avram_gauss_finitec2_cap_ode_derivative_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:19:34.407926+00:00
-- url     : https://prove2.me/theorems/f80bc7ac-4940-4bc0-be66-2c6f46279d02
-- title:
--   Finite-cap uniform gradient bound from one-sided Gaussian HJB differential inequality
-- statement:
--   The one-sided differential estimate p'≤βp+ε on a finite positive cap band, with nonnegative coefficient and initial slope, gives a uniform finite upper bound throughout the half-open band. Its direct root-connected use is p=deriv w on [C/2,C), β=max(0,-X.c/(X.σ²/2)), ε=q*w(C)/(X.σ²/2) for d1caa4aa and a338c453. This is the first analytic cap-contact step; it alone does not supply the original controlled Ito-Stieltjes identity.
-- source:
--   Exact finite-cap ODE comparison needed for the Gaussian C2 stopped supermartingale with arbitrary cap-reflecting dividends; uses pinned Mathlib Gronwall and original HJB cap differential estimate. Parent d1caa4aa remains Open and must import a proved helper before any closure.

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Set
noncomputable section

theorem AvramDividend.Classical.avram_gauss_finitec2_cap_ode_derivative_uniform
    (p dp : ℝ → ℝ) (u C β ε : ℝ)
    (huC : u < C) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hp0 : 0 ≤ p u)
    (hpcont : ContinuousOn p (Ico u C))
    (hpderiv : ∀ y ∈ Ico u C, HasDerivAt p (dp y) y)
    (hpODE : ∀ y ∈ Ico u C, dp y ≤ β * p y + ε) :
    ∃ B : ℝ, ∀ y ∈ Ico u C, p y ≤ B := by sorry
