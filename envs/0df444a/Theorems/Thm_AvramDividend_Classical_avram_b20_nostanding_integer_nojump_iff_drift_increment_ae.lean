-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b20_nostanding_integer_nojump_iff_drift_increment_ae
-- name    : AvramDividend.Classical.avram_b20_nostanding_integer_nojump_iff_drift_increment_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T21:23:44.061222+00:00
-- url     : https://prove2.me/theorems/fb2bc232-8a54-48e5-86d5-17cf90b692c8
-- title:
--   Non-Standing original finite-activity no-jump iff drift law simultaneously on all integer intervals
-- statement:
--   For any bounded-variation spectrally negative Lévy process with finite negative-jump intensity, on one common full-measure event all integer clock intervals are exactly drift-linear precisely when the original marked jump measure records zero negative jumps. This is simultaneous for all integer endpoints, without Standing, and provides a countable-time skeleton for the original path decomposition.
-- source:
--   Countable AE intersection of Proved original source-exact fixed-clock no-jump event equality with drift interval identity avram_wave4_04a_bv_actual_intrinsic_zero_count_event_ae_eq_drift_increment (d18331ab). The child strengthens simultaneous quantification, introduces no new stochastic hypothesis or source model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b20_nostanding_integer_nojump_iff_drift_increment_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ (s t : ℕ), s ≤ t →
      (((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s : ℝ≥0) (t : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ↔
        X.X (t : ℝ≥0) ω - X.X (s : ℝ≥0) ω =
          (((t : ℝ≥0) : ℝ) - ((s : ℝ≥0) : ℝ)) * X.drift) := by sorry
