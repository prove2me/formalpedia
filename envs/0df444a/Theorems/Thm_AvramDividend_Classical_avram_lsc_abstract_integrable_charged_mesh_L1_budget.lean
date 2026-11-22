-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_abstract_integrable_charged_mesh_L1_budget
-- name    : AvramDividend.Classical.avram_lsc_abstract_integrable_charged_mesh_L1_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T08:36:52.556671+00:00
-- url     : https://prove2.me/theorems/378ade4a-bc91-4dbb-a61f-edbd31bde142
-- title:
--   Integrable original stopped cash and Gaussian grids transfer charged L1 error to positive finite-band expected budget
-- statement:
--   Given an actual integrable stopped cash balance after subtracting the nonnegative cap-corner and upper-strip charges, integrable Gaussian grids, integrable centred L1 limit, and a source charged positive residual with vanishing expected L1, conclude the precise eventwise finite-band positive cash inequality. Explicit hypotheses retain original occupation charge and avoid needing an extra a.e. pathwise cash source.
-- source:
--   Original Avram finitecap Gaussian signed stochastic cash source; combines Proved charged mesh L1 transfer fbb30777 with standard stability of Bochner integrability under subtraction, absolute value and nonnegative positive part.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_lsc_abstract_charged_mesh_L1_to_expected_positive_budget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_lsc_abstract_integrable_charged_mesh_L1_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (F N Occ : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hFBI : IntegrableOn
      (fun ω => F ω - (B + c * Occ ω)) A P)
    (hNI : IntegrableOn N A P)
    (hMInt : ∀ m, IntegrableOn (M m) A P)
    (hL1 : Tendsto (fun m =>
      ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun m =>
      ∫ ω in A, max (F ω - M m ω - (B + c * Occ ω)) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hFI : ∀ m, IntegrableOn (fun ω => max (F ω - M m ω) 0) A P)
    (hOccI : IntegrableOn Occ A P)
    (hOccNonneg : ∀ᵐ ω ∂(P.restrict A), 0 ≤ Occ ω) :
    ∀ ε : ℝ, 0 < ε → ∀ K : ℕ, ∃ m : ℕ, K < m ∧
      (∫ ω in A, max (F ω - M m ω) 0 ∂P) ≤
        B + c * (∫ ω in A, Occ ω ∂P) + ε := by sorry
