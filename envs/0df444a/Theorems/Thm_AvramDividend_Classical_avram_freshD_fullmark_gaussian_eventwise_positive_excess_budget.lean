-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_fullmark_gaussian_eventwise_positive_excess_budget
-- name    : AvramDividend.Classical.avram_freshD_fullmark_gaussian_eventwise_positive_excess_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T18:36:05.821868+00:00
-- url     : https://prove2.me/theorems/6e2f6a47-975f-4215-b46c-4039dd3d1d89
-- title:
--   Vanishing original Gaussian plus fully marked compensated positive cash excess yields initial-event budget
-- statement:
--   A quantitative analytic source bridge for the Avram original mixed Gaussian/nonlinear full-negative-mark stopped cash certificate: for every initial event and arbitrarily small positive integrated excess, there are two integrable source gains (Gaussian and complete nonlinear negative-mark) with zero eventwise means. Then the actual integrable reward has eventwise initial budget at most c times event probability. No already-sought expected budget is assumed: the assumption instead requires a quantitative positive-part source approximation, with two genuinely centred channel witnesses.
-- source:
--   Corrected finite-activity mixed Ito route to root mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, b98df424. Elementary integral inequality: u≤max(u,0); source centring cancels the two gains and arbitrary ε forces expected budget. A later source child must construct G and J from actual Gaussian predictable integrals and the original full nonlinear compensated negative marks, rather than treating abstract centring as an Ito certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_fullmark_gaussian_eventwise_positive_excess_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (F : Ω → ℝ) (c : ℝ) (hFI : Integrable F P)
    (hApprox : ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∀ ε : ℝ, 0 < ε →
      ∃ (G J : Ω → ℝ),
        IntegrableOn G A P ∧ IntegrableOn J A P ∧
        (∫ ω in A, G ω ∂P) = 0 ∧
        (∫ ω in A, J ω ∂P) = 0 ∧
        IntegrableOn (fun ω => max (F ω - c - G ω - J ω) 0) A P ∧
        (∫ ω in A, max (F ω - c - G ω - J ω) 0 ∂P) ≤ ε) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F ω ∂P) ≤ c * (P A).toReal := by sorry
