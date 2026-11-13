-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b22_initial_event_finite_mesh_vanishing_error_budget
-- name    : AvramDividend.Classical.avram_b22_initial_event_finite_mesh_vanishing_error_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:30:21.411205+00:00
-- url     : https://prove2.me/theorems/7fd433cc-ebca-43ea-b84a-649c75ec354f
-- title:
--   Original stopped finite-mesh aggregate cash inequality passes through vanishing local expected errors
-- statement:
--   An exact stopped reward dominated on every mesh by initial HJB value, an aggregate locally centred gain and one signed physical mesh error satisfies the initial-event expected budget whenever the errors can be made arbitrarily small in mean. No separate global noise moment estimates are required.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i), stopped Ito-Meyer localisation and expected dividend cash inequality, arXiv math/0702893.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b21_initial_event_local_aggregate_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b22_initial_event_finite_mesh_vanishing_error_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (F : Ω → ℝ) (hFI : IntegrableOn F A P)
    (M Err : ℕ → Ω → ℝ)
    (hMI : ∀ n, IntegrableOn (M n) A P)
    (hEI : ∀ n, IntegrableOn (Err n) A P)
    (hMzero : ∀ n, (∫ ω in A, M n ω ∂P) = 0)
    (hBound : ∀ n, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ b + M n ω + Err n ω)
    (hErr : ∀ ε : ℝ, 0 < ε →
      ∃ n, (∫ ω in A, Err n ω ∂P) ≤ ε) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by sorry
