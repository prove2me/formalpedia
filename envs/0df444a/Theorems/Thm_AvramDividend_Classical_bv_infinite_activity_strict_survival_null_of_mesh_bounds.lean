-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_strict_survival_null_of_mesh_bounds
-- name    : AvramDividend.Classical.bv_infinite_activity_strict_survival_null_of_mesh_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:26:56.656521+00:00
-- url     : https://prove2.me/theorems/f13504cf-9102-4b82-ad42-406051661492
-- title:
--   An actual infinite-activity bounded-variation Lévy zero-barrier reflected-survival event is null once its expected mesh bound holds
-- statement:
--   For a bounded-variation spectrally negative Lévy process with infinite negative jump intensity, consider any positive horizon T. If the expected physical-drift deficit restricted to strict reflected survival is integrable and is bounded by a uniform mesh exponential error C(1-exp(-delta_n*(drift*theta_n-psi(theta_n)))) along reciprocal-frequency meshes, then strict survival past T has measure zero. Uses the accepted BV drift-deficit almost-sure upper bound, zero-atom theorem, inverse-frequency exponent asymptotic, exponential continuity and null-event expectation lemma.
-- source:
--   Proved bv_actual_levy_drift_upper_ae_fixed_time, bv_infinite_activity_drift_deficit_zero_atom, bv_inverse_frequency_mesh_gap_tendsto_zero, mesh_exponential_gap_tendsto_zero, vanishing_expected_deficit_bound_forces_null_event.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_zero_atom
import Theorems.Thm_AvramDividend_Classical_bv_inverse_frequency_mesh_gap_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_mesh_exponential_gap_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_vanishing_expected_deficit_bound_forces_null_event
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Measure.Real

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_strict_survival_null_of_mesh_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (δ θ : ℕ → ℝ) (c C : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθne : ∀ n, θ n ≠ 0)
    (hProduct : ∀ n, δ n * θ n = c)
    (hInt : Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω)) P)
    (hBound : ∀ n : ℕ,
      (∫ ω, {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω) ω ∂P) ≤
      C * (1 - Real.exp (-(δ n * (X.drift * θ n - X.ψ (θ n)))))) :
    P {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω} = 0 := by sorry
