-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_uniform_ceil_pair_lintegral_limit
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_uniform_ceil_pair_lintegral_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:46:04.87495+00:00
-- url     : https://prove2.me/theorems/725de0e6-ad6f-4759-869b-dfd304676147
-- title:
--   Original physical chronological ceiling-grid pair expectation tends to half the squared finite negative-band Lévy rate
-- statement:
--   Under the genuine original spectrally negative Lévy source, positive physical horizon and negative-band marked finite times, the expected ENNReal ceiling-index chronological pair count converges to half the squared original T-times-Levy-band rate. Prove by the same-original-source physical marked-grid identity, finite-grid predictable compensation and deterministic triangular-rate limit; no equality-in-law surrogate.
-- source:
--   The exact missing source-expectation premise of Proved 2325c9f1 and Open 978af370. Source inputs: Proved original physical ceil pair identity 32061d3a and 3bf8aa71; original uniform-grid compensator 6e416dba; original all-mesh measurability f09bb8b3; finite-band quadratic triangular rate limit 83db5394; same original X, P, filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_uniform_ceil_pair_lintegral_limit
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
