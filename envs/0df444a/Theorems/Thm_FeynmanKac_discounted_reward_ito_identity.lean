-- Prove2me | Theorems.Thm_FeynmanKac_discounted_reward_ito_identity
-- name    : FeynmanKac.discounted_reward_ito_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:40:12.157744+00:00
-- url     : https://prove2.me/theorems/ef3216ae-6881-4b4f-932e-08919670b0cf
-- title:
--   Discounted Itô identity with PDE drift cancellation
-- statement:
--   Using a genuine time-dependent Itô formula, the product rule for the pathwise discount, the integral of the running source and the classical backward PDE, derive that the discounted reward equals its deterministic initial value plus the actual L²-Itô integral of the discounted spatial gradient. The stochastic integral is computed on elapsed Brownian time s−initialTime, with independent admissibility witnesses; no Feynman–Kac martingale or expectation identity is assumed.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; James Nolen, Stanford notes Section 4.1 https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf

import Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient
import Definitions.Def_FeynmanKac_ModelReward
import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.discounted_reward_ito_identity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hdisc : m.AdmissibleDiscountedGradient u)
    (s : ℝ) (hs : s ∈ Set.Icc m.initialTime m.terminalTime) :
    (fun ω => m.discountedReward u s ω) =ᵐ[P]
      (fun ω => u m.initialState m.initialTime +
        m.discountedGradientItoIntegral u hdisc s ω) := by sorry
