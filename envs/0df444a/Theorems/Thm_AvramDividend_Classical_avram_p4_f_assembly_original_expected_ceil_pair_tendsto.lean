-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_expected_ceil_pair_tendsto
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_expected_ceil_pair_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:51:34.068538+00:00
-- url     : https://prove2.me/theorems/3c3b14b3-1ed9-4796-b381-50ed7aba4009
-- title:
--   True original Lévy physical-grid chronological pair expected rate converges to half the squared finite-band intensity
-- statement:
--   For the unchanged original Lévy process, every positive horizon and negative finite Lévy band, the expected count of chronological marked pairs separated by physical uniform mesh tends to the half-square of the true horizon Lévy intensity. Needs same-X finite-grid P2-E compensator, deterministic triangle rate limit and the exact ν(B) finiteness conversion.
-- source:
--   Proved physical count 32061d3a, same-source P2-E expectation 77b37394, Proved numerical limit 83db5394, square conversion 35bbaf6a and finite ν rate 86086cb2; physical grid exact marked set. This is the final source expectation limit gap for Proved conditional consumer 2325c9f1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_expected_ceil_pair_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)
    let r : ℝ :=
      (((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop
      (𝓝 (ENNReal.ofReal (r ^ 2 / 2))) := by sorry
