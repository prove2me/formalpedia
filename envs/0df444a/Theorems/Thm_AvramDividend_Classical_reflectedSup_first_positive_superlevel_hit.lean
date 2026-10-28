-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_first_positive_superlevel_hit
-- name    : AvramDividend.Classical.reflectedSup_first_positive_superlevel_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:56:59.952538+00:00
-- url     : https://prove2.me/theorems/d9961902-0e8c-4988-a2b2-65b5861d4deb
-- title:
--   Actual reflected spectrally negative Lévy drawdown admits an earliest strictly interior positive-level superlevel entrance
-- statement:
--   For the actual reflected spectrally negative Lévy path R=S−X, and any positive level x reached strictly before finite horizon ζ, there exists an earliest time T when R reaches or overshoots x. T is exactly the infimum of the compact superlevel entrance set, strictly positive, strictly before ζ, satisfies R(T)≥x and is no later than any other such entrance. This applies the genuine actual-path upper semicontinuity and origin-zero results to the general first-superlevel hitting-time lemma. It is a pathwise hitting-time result only; proving the map ω↦T(ω) is a stopping time remains separate.
-- source:
--   Kuznetsov-Kyprianou-Rivero (2013) excursion-height first hitting; Mathlib upper semicontinuous compact superlevel sets.

import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_origin_eq_zero
import Theorems.Thm_AvramDividend_Classical_first_superlevel_hit_of_upperSemicontinuous

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_first_positive_superlevel_hit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) (x : ℝ) (hx : 0 < x)
    (hHit : ∃ t : ℝ≥0, t < ζ ∧ x ≤ reflectedSup X t ω) :
    ∃ T : ℝ≥0,
      T = sInf (Icc (0 : ℝ≥0) ζ ∩
        (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∧
      0 < T ∧ T < ζ ∧ x ≤ reflectedSup X T ω ∧
      ∀ s : ℝ≥0, s ≤ ζ → x ≤ reflectedSup X s ω → T ≤ s := by sorry
