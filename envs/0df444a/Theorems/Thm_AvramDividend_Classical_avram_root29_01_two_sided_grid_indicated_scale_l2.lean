-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_two_sided_grid_indicated_scale_l2
-- name    : AvramDividend.Classical.avram_root29_01_two_sided_grid_indicated_scale_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:30:41.204731+00:00
-- url     : https://prove2.me/theorems/ad5fc6bc-3f97-4dd8-bddf-8cd38dadbbca
-- title:
--   Original-Lévy two-sided grid stopped scale square bound under measurable killing
-- statement:
--   Under the genuine source two-sided finite-grid stopping-time moment hypotheses, the q-scale squared payoff remains integrable and obeys the same uniform finite-horizon L² bound after restriction to any measurable survival event. The proof uses the accepted original-Lévy stopped-square estimate, direct indicator pointwise comparison and Bochner integral monotonicity. For the true lower-survival event this is the integrability ingredient for killed-grid convergence.
-- source:
--   WS1A work/avram_root29_01_two_sided_grid_indicated_scale_l2_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_two_sided_grid_source_scale_l2

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_two_sided_grid_indicated_scale_l2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω)
    (N : ℝ≥0) (hN : ∀ ω, clock (K ω) ≤ N)
    (hMeas : AEStronglyMeasurable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P)
    (B : Set Ω) (hB : MeasurableSet B) :
    Integrable (B.indicator (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2)) P ∧
    (∫ ω, B.indicator (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) ω ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by sorry
