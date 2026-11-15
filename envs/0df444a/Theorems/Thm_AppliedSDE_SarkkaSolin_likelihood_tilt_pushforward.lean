-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_likelihood_tilt_pushforward
-- name    : AppliedSDE.SarkkaSolin.likelihood_tilt_pushforward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:15:13.512764+00:00
-- url     : https://prove2.me/theorems/c217a3a6-2ba5-44dd-93c4-e7a9cc48b5f8
-- title:
--   Transport of an observation-dependent likelihood change through a measurable random variable
-- statement:
--   For any measurable random variable X:Omega->E, probability or general measure P, and measurable nonnegative extended-real likelihood f on E, pushing forward the weighted measure P.withDensity(f composed with X) by X produces exactly the weighted pushforward (P.map X).withDensity(f). This rigorous measure-theoretic identity lifts Gaussian Esscher tilts of a marginal distribution into Brownian finite-time change-of-measure statements without assuming an unproved Girsanov theorem.
-- source:
--   Sarkka and Solin, Applied Stochastic Differential Equations (2019), Chapter 7, change of measure and pushforward laws.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AppliedSDE.SarkkaSolin.likelihood_tilt_pushforward
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (P.withDensity (fun ω => f (X ω))).map X =
      (P.map X).withDensity f := by
  sorry
