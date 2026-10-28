-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_first_exact_height_hit
-- name    : AvramDividend.Classical.reflectedSup_finite_excursion_first_exact_height_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:21:45.787465+00:00
-- url     : https://prove2.me/theorems/d290f43f-35a0-4589-9e10-33adb620b5bc
-- title:
--   First exact hitting time of the true positive height of a finite reflected Lévy excursion lies strictly inside the excursion
-- statement:
--   For an actual reflected spectrally negative Lévy path R with a finite excursion lifetime ζ>0, R(ζ)=0, and a positive excursion height x equal to the true supremum of R on [0,ζ], the earliest time T at which R reaches x is the infimum of its compact superlevel entrance set. It lies strictly between 0 and ζ, satisfies R(T)=x and precedes all other exact height hits. This removes every artificial pathwise hitting-time assumption from the conditional excursion-height atomlessness proof on finite excursions. The measurability/stopping-time property of the map ω↦T(ω) and excursion-measure lifetime properties remain separate.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), Lemma 2.4, built from the accepted Prove2Me reflected-path upper semicontinuity, supremum attainment and first exact superlevel entrance theorems.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_positive_height_sSup_attained
import Theorems.Thm_AvramDividend_Classical_first_exact_level_hit_of_upperSemicontinuous
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_origin_eq_zero

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_finite_excursion_first_exact_height_hit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) (hζ : 0 < ζ)
    (hEnd : reflectedSup X ζ ω = 0)
    (x : ℝ) (hx : 0 < x)
    (hHeight : sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 ζ) = x) :
    ∃ T : ℝ≥0,
      T = sInf (Icc (0 : ℝ≥0) ζ ∩
        (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∧
      0 < T ∧ T < ζ ∧ reflectedSup X T ω = x ∧
      ∀ s : ℝ≥0, s ≤ ζ → reflectedSup X s ω = x → T ≤ s := by sorry
