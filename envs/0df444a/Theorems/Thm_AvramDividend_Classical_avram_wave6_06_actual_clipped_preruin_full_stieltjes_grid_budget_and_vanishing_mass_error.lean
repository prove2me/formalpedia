-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_clipped_preruin_full_stieltjes_grid_budget_and_vanishing_mass_error
-- name    : AvramDividend.Classical.avram_wave6_06_actual_clipped_preruin_full_stieltjes_grid_budget_and_vanishing_mass_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:19:40.237078+00:00
-- url     : https://prove2.me/theorems/29a2b4cf-20f0-4dc3-a914-3d5f96ddaf77
-- title:
--   Actual original ruin-localised clipped-grid full Stieltjes right-endpoint budget with vanishing mass error
-- statement:
--   For the original Lévy process X and admissible dividend D, fix one sample path stopped strictly before ruin (or at zero), a bounded local clock, and monotone source grids covering that clock. The actual clipped pre/post-dividend reserve drop bounds the whole genuine exponentially discounted original Stieltjes cash on (0,τ], with only q times mesh times full dividend mass as error. That exact pathwise full-mass error tends to zero. All atomic, diffuse and singular-continuous dividends and simultaneous source/dividend jumps remain included, and no source stochastic-chain-rule premise is hidden.
-- source:
--   Avram-Palmowski-Pistorius Proposition 4(i) exact chronological dividend measure; already Proved b0ef57b5 original finite-grid mass bound, 19dce1c2 moving-grid vanishing error, 572b8d66 clipping nonexpansive; independently identifies the stopped-grid dividend leg without presuming mixed Lévy Ito–Meyer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_preruin_full_grid_right_endpoint_mesh_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_moving_grid_full_dividend_mass_mesh_error_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_actual_clipped_preruin_full_stieltjes_grid_budget_and_vanishing_mass_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτT : τ ω ≤ T)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (hzero : ∀ n, u n 0 = 0)
    (hcover : ∀ n, τ ω ≤ u n (k n))
    (mesh : ℕ → ℝ) (hm : ∀ n, 0 ≤ mesh n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ mesh n)
    (hmesh0 : Tendsto mesh atTop (𝓝 0)) :
    (let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
     (∀ n,
      (∫⁻ s in Ioc (0 : ℝ) (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      (∑ i ∈ Finset.range (k n),
        ENNReal.ofReal (Real.exp (-(q * (v n (i + 1) : ℝ)))) *
          ENNReal.ofReal
            (V (x + X.X (v n (i + 1)) ω - rightLimit D (v n i) ω) -
             V (x + X.X (v n (i + 1)) ω - rightLimit D (v n (i + 1)) ω))) +
        ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ))) ∧
     Tendsto
       (fun n =>
         (ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ))).toReal)
       atTop (𝓝 0)) := by sorry
