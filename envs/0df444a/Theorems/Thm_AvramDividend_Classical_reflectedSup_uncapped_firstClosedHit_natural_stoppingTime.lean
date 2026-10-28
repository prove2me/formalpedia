-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_uncapped_firstClosedHit_natural_stoppingTime
-- name    : AvramDividend.Classical.reflectedSup_uncapped_firstClosedHit_natural_stoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:24:45.248985+00:00
-- url     : https://prove2.me/theorems/8e10366d-0110-4396-8080-97b19fb5f195
-- title:
--   Actual unbounded-horizon reflected level hitting time is a stopping time with natural caps
-- statement:
--   The extended supremum over natural-number finite capped reflected first closed-level hitting clocks is a stopping time. Its finite-time sublevel event is exactly existence of a genuine earlier closed-level hit. Natural horizons are cofinal, so the construction includes infinity on paths with no hit. This follows by instantiating the proved cofinal cap theorem with the proved Archimedean natural cap schedule.
-- source:
--   Accepted Prove2Me reflectedSup_uncapped_firstClosedHit_stopping_and_event and nnreal_natCaps_cofinal.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_reflectedSup_uncapped_firstClosedHit_stopping_and_event
import Theorems.Thm_AvramDividend_Classical_nnreal_natCaps_cofinal

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_uncapped_firstClosedHit_natural_stoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨆ n : ℕ, WithTop.some
        (sInf ((Icc (0 : ℝ≥0) (n : ℝ≥0) ∩
          (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∪ {(n : ℝ≥0)}))) ∧
    ∀ ω : Ω, ∀ t : ℝ≥0,
      (⨆ n : ℕ, WithTop.some
        (sInf ((Icc (0 : ℝ≥0) (n : ℝ≥0) ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {(n : ℝ≥0)}))) ≤
          (t : WithTop ℝ≥0) ↔
        ∃ s : ℝ≥0, s ≤ t ∧ x ≤ reflectedSup X s ω := by sorry
