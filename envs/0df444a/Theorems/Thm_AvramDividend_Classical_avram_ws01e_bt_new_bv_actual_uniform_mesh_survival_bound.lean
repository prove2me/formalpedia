-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_bv_actual_uniform_mesh_survival_bound
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_bv_actual_uniform_mesh_survival_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:34:45.736956+00:00
-- url     : https://prove2.me/theorems/d71c5226-3589-425b-abae-9b3b2d7f1cf8
-- title:
--   Actual BV Lévy zero-barrier strict-survival expectation bound on a calibrated uniform time mesh
-- statement:
--   Let X be an actual spectrally negative Lévy process satisfying Standing and bounded variation. For any positive horizon T and positive natural mesh count N with 2 X.drift T ≤ N, bound the P-expectation of the nonnegative physical drift deficit on the strict reflected zero-barrier survival event by 4 X.drift T times the exact one-cell exponential deficit 1-exp(-δ (X.drift θ-ψ θ)), where δ=T/N and θ=1/(2 X.drift δ). This unconditional source-Lévy inequality follows by the genuine accepted BV mesh survival bound after proving the standard grid geometry and actual adapted-path cell measurability and integrability. No arbitrary stochastic independence or claimed Lévy-Itô decomposition is assumed.

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_bv_mesh_grid_calibration
import Theorems.Thm_AvramDividend_Classical_bv_survival_mesh_bound_normalized_exponent
import Theorems.Thm_AvramDividend_Classical_bv_actual_grid_exponential_integrability
import Theorems.Thm_AvramDividend_Classical_bv_actual_survival_deficit_integrable
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Probability.Process.Adapted

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_bt_new_bv_actual_uniform_mesh_survival_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : 0 < T)
    (N : ℕ) (hN : 0 < N)
    (hLarge : 2 * X.drift * (T : ℝ) ≤ (N : ℝ)) :
    (let δ : ℝ≥0 := T / (N : ℝ≥0)
     let a : ℝ := X.drift * (δ : ℝ)
     let θ : ℝ := 1 / (2 * a)
     (∫ ω, {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
       (fun ω => (T : ℝ) * X.drift - X.X T ω) ω ∂P) ≤
       (4 * X.drift * (T : ℝ)) *
         (1 - Real.exp (-((δ : ℝ) * (X.drift * θ - X.ψ θ))))) := by sorry
