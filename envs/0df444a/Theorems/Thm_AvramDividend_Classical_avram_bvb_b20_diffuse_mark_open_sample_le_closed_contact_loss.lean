-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_diffuse_mark_open_sample_le_closed_contact_loss
-- name    : AvramDividend.Classical.avram_bvb_b20_diffuse_mark_open_sample_le_closed_contact_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:55:43.02344+00:00
-- url     : https://prove2.me/theorems/c7b0c95b-4c4f-4e4e-ba18-07dff081f555
-- title:
--   One-sided original negative-mark open-grid loss stays below nearby closed-cap loss
-- statement:
--   A sampled negative-mark loss restricted to the open cap is uniformly bounded above by the full closed-cap loss at a nearby reserve, with arbitrary positive error. This retains the correct one-sided behaviour at zero and upper-cap contact and uses finite diffuse mark intensity.
-- source:
--   Local contact-safe marked-compensator inequality necessary for original phys95 and later-ruin uniform-grid reverse-Fatou comparison.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_diffuse_mark_open_sample_le_closed_contact_loss
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (ν : Measure ℝ) (hνfinite : ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, ν {a} = 0)
    (s : Set ℝ) (hs : IsCompact s)
    (hsCap : s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C})
    (hneg : ∀ b ∈ s, (∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν) ≤ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, ∀ b ∈ s, |a - b| < δ →
      (if 0 < a ∧ ENNReal.ofReal a < C then
        -(∫ z in Iio (0 : ℝ), w (a + z) - w a ∂ν) else 0) ≤
      -(∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν) + ε := by sorry
