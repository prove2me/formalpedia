-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ou_deterministic_integrand_energy
-- name    : AppliedSDE.SarkkaSolin.ou_deterministic_integrand_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:02:05.046563+00:00
-- url     : https://prove2.me/theorems/48d0c57c-5f16-4feb-a726-aac0a9bed233
-- title:
--   Exact deterministic OU Itô-integrand energy over a finite horizon
-- statement:
--   Let rate>0, q≥0, and T≥0. The deterministic Ornstein–Uhlenbeck stochastic-integral integrand H(s)=sqrt(q)exp(-rate(T-s)) has time-integrated squared magnitude q(1-exp(-2 rate T))/(2 rate). This is the exact deterministic energy term required by Chapter 3's Itô isometry and transition-variance milestone bc5cda7c-dc7b-488a-b1bd-b5d8f88d30f8. The result uses explicit exponential differentiation and the interval fundamental theorem of calculus; no stochastic moment identities are assumed.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 3 (Ornstein–Uhlenbeck transition variance). https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory

theorem AppliedSDE.SarkkaSolin.ou_deterministic_integrand_energy
    (rate q T : ℝ) (hrate : 0 < rate) (hq : 0 ≤ q) (hT : 0 ≤ T) :
    (∫ s in (0 : ℝ)..T,
      (Real.sqrt q * Real.exp (-rate * (T - s))) ^ 2) =
      q / (2 * rate) * (1 - Real.exp (-2 * rate * T)) := by
  sorry
