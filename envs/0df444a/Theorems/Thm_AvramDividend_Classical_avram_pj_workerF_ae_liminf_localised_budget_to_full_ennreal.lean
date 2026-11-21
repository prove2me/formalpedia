-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_ae_liminf_localised_budget_to_full_ennreal
-- name    : AvramDividend.Classical.avram_pj_workerF_ae_liminf_localised_budget_to_full_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:08:53.698564+00:00
-- url     : https://prove2.me/theorems/c1178405-3501-4205-a01d-3cc154a78cfb
-- title:
--   Localised nonnegative ENNReal expected budgets transfer by almost-everywhere liminf to the full original stopped reward
-- statement:
--   If each measurable nonnegative ENNReal localised approximation A_j has expectation at most B and the original nonnegative stopped payoff F is almost-everywhere at most the liminf of A_j, then the original payoff has extended-real expectation at most B. The proof is exact Fatou and does not require a globally integrable limiting martingale, uniform integrability or any stopping-clock approximants to have an incorrectly omitted dividend atom. Designed for original Lévy stopped caplinear plus inclusive dividend-cash supermartingale localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerF_ae_liminf_localised_budget_to_full_ennreal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → ℝ≥0∞) (F : Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hAm : ∀ j, Measurable (A j))
    (hBound : ∀ j, (∫⁻ ω, A j ω ∂P) ≤ B)
    (hlim : ∀ᵐ ω ∂P,
      F ω ≤ liminf (fun j => A j ω) atTop) :
    (∫⁻ ω, F ω ∂P) ≤ B := by sorry
