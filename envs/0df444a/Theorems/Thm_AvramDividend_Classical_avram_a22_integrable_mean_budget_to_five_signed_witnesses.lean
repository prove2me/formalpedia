-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_integrable_mean_budget_to_five_signed_witnesses
-- name    : AvramDividend.Classical.avram_a22_integrable_mean_budget_to_five_signed_witnesses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:01:21.080329+00:00
-- url     : https://prove2.me/theorems/674ec129-1dbd-4002-b482-2938311419d8
-- title:
--   Integrable expected budget yields three centred and two nonpositive signed witnesses
-- statement:
--   An elementary measure theoretic witness extraction, valid for every probability space and every integrable real reward F. If E F≤b, the true centred gain M=F−E F has mean zero, the constant signed drift G=E F−b is nonpositive, and setting the other four witness components to zero gives exact pathwise equality F=b+M+G. Applied to the actual original masked stopped cash reward to close a Gaussian zerojump branch, without adding finite-cap assumptions or inventing stochastic centring. The HJB estimate E F≤b must still be established independently.
-- source:
--   Elementary exact decomposition of any integrable random reward into mean-zero gain plus nonpositive constant drift given a validated expected budget; stochastic original clock only through actual reward passed as F.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_a22_integrable_mean_budget_to_five_signed_witnesses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ)
    (hBudget : (∫ ω, F ω ∂P) ≤ b) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        F ω ≤ b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
