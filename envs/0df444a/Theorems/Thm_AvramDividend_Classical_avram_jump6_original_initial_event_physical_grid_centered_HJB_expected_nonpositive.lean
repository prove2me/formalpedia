-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_initial_event_physical_grid_centered_HJB_expected_nonpositive
-- name    : AvramDividend.Classical.avram_jump6_original_initial_event_physical_grid_centered_HJB_expected_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T20:46:39.686966+00:00
-- url     : https://prove2.me/theorems/7a944609-0827-4aa0-a0ba-350581407e80
-- title:
--   Original initial-event stopped predictable physical Lévy martingale and HJB right-payment ledger have nonpositive conditional expectation
-- statement:
--   For any event A measurable at the right-continuous original time-zero filtration, combine the actual physical stopped HJB generator drift and zero/strict-pre-ruin right-dividend corrections with a finite grid of original Lévy increments centered against their true means and weighted by predictable coefficients. The event-masked martingale contribution has exactly zero expectation, and the event-masked signed physical source has nonpositive expectation. This establishes the correct initial-event expected finite-grid source bound used to derive the positive-clock Avram stopped-reward HJB inequality. The nonlinear Ito-Meyer Taylor remainder, Poisson compensation and physical mesh limit remain mathematical obligations, not assumptions hidden in the conclusion.
-- source:
--   Proved right-continuous original-X stopped-grid martingale c26cb776-25c7-44d3-9139-4604a0a787bf, Proved original physical HJB/rightpayment b239 316fb152-4993-4218-b6a2-b24fe4d6499c, initial event measurability bce62e25. This directly constructs an event-masked signed expected mesh source with no dependency on still-awaiting-publication event-cell helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_rightCont_predictable_stopped_grid_levy_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_jump6_original_initial_event_physical_grid_centered_HJB_expected_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (σ : Ω → ℝ≥0) (n m : ℕ)
    (active : Ω → ℕ → Bool)
    (hInterior : ∀ ω, ∀ i ∈ Finset.range m, active ω i = true →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      let z := riskProcess X x D (v i) ω
      0 < z ∧ ENNReal.ofReal z < C)
    (hTimes : ∀ ω, ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      v i ≤ v (i + 1))
    (R : Ω → Finset ℝ≥0)
    (hPre : ∀ ω, ∀ u ∈ R ω,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω)
    (B : Ω → ℝ)
    (hBsource : ∀ ω, B ω = ((∑ i ∈ Finset.range m,
          if active ω i then
            Real.exp (-(q * (min ((i : ℝ≥0) *
              ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω) : ℝ))) *
              ((min (((i + 1 : ℕ) : ℝ≥0) *
                ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω) : ℝ) -
               (min ((i : ℝ≥0) *
                ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω) : ℝ)) *
              (X.generator w (riskProcess X x D
                  (min ((i : ℝ≥0) *
                    ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω)) ω) -
                q * w (riskProcess X x D
                  (min ((i : ℝ≥0) *
                    ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω)) ω))
          else 0) +
      (∑ u ∈ R ω, Real.exp (-(q * (u : ℝ))) *
        ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))))))
    (hBI : Integrable B P)
    (grid : ℕ → ℝ≥0)
    (hgrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hHPast : ∀ i, Measurable[(𝓕.rightCont) (grid i)] (H i))
    (hHI : ∀ i, Integrable (H i) P)
    (hXI : ∀ i,
      Integrable (X.X (grid (i + 1) - grid i)) P)
    (hCellI : ∀ i ∈ Finset.range m, Integrable
      (fun ω => (if ω ∈ A then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P))) P) :
    let M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m, (if ω ∈ A then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P))
    Integrable (fun ω => M ω + (if ω ∈ A then B ω else 0)) P ∧
      (∫ ω, M ω + (if ω ∈ A then B ω else 0) ∂P) ≤ 0 := by sorry
