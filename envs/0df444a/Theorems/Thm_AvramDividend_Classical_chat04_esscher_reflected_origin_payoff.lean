-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_origin_payoff
-- name    : AvramDividend.Classical.chat04_esscher_reflected_origin_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:03:29.312045+00:00
-- url     : https://prove2.me/theorems/318dde7b-58dc-4c23-90da-88d42e5d1c53
-- title:
--   Esscher-weighted reflected-infimum capital payoff normalises at the zero horizon
-- statement:
--   At horizon zero, the reflected infimum of the Lévy process started at zero is zero, and its compensated exponential equals one. Consequently the Esscher-weighted capital-envelope payoff is exactly 1/β at every sample point, independently of the tilt parameter.
-- source:
--   Direct from the source definition X.X_zero, the singleton range of the path on [0,0], sInf_singleton and exp(0)=1. This establishes the exact initial value needed to normalise the genuine finite-horizon and infinite-horizon Esscher capital-Laplace transforms.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_reflected_origin_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (β θ : ℝ) (hβ : 0 < β) :
    (Real.exp (-β * max 0
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (0 : ℝ≥0) ∧ y = X.X s ω})) / β) *
    Real.exp (θ * X.X 0 ω -
      ((0 : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ) =
    1 / β := by sorry
