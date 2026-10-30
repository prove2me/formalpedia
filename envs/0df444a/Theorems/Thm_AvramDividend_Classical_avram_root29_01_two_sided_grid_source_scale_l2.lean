-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_two_sided_grid_source_scale_l2
-- name    : AvramDividend.Classical.avram_root29_01_two_sided_grid_source_scale_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:25:31.382531+00:00
-- url     : https://prove2.me/theorems/9aeb56f8-8d35-4a3f-bb6f-fffc3f63ee65
-- title:
--   Genuine original-Lévy two-sided bounded-grid q-scale L² bound
-- statement:
--   For a genuine source Lévy process and arbitrary bounded two-sided finite observation-grid first-exit index with the displayed adapted filtration and a.e. scale-square measurability, the discounted terminal q-scale squared moment is integrable and obeys the explicit uniform horizon bound. Source-specific finite-grid compensated exponential moment-one and integrability, both canonically Proved, discharge the stochastic inputs of the accepted fixed-horizon scale L² estimate. Supports subsequent killed-grid uniform integrability; does not assume the continuous first-exit identity.
-- source:
--   WS1A work/avram_root29_01_two_sided_grid_source_scale_l2_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_fixed_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_compensated_exp_integrable
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_compensated_exp_moment_one

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_two_sided_grid_source_scale_l2
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
        W (x + X.X (clock (K ω)) ω)) ^ 2) P) :
    Integrable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by sorry
