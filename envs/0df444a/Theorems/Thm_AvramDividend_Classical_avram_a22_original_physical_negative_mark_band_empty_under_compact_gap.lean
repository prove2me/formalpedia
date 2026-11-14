-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_physical_negative_mark_band_empty_under_compact_gap
-- name    : AvramDividend.Classical.avram_a22_original_physical_negative_mark_band_empty_under_compact_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:08:05.728845+00:00
-- url     : https://prove2.me/theorems/c65d31ab-ff35-43bf-9deb-d578106d6594
-- title:
--   Original physical negative-mark source is empty on narrow bands below the actual compact jump gap
-- statement:
--   For one original sample path with every nonzero negative jump bounded above by a negative pathwise number -δ on [0,T], any physical cutoff of width 1/(n+1) strictly less than δ has no actual negative jump mark in the corresponding open nearzero band. Uses only source jump ΔX and deterministic order; no replacement noise or stochastic cutoffs.
-- source:
--   Actual original finite-activity jump gap mathematical consequence; will combine with original finite marked jump source c6cc76c9 and source band integration. Kyprianou Chapter 2 finite-activity truncation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_physical_negative_mark_band_empty_under_compact_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hGap : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -δ)
    (n : ℕ) (hN : 1 / ((n : ℝ) + 1) < δ) :
    ∀ u : ℝ≥0, 0 < u → u ≤ T →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∉
        Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ) := by sorry
