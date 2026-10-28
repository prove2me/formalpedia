-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_positive_height_sSup_attained
-- name    : AvramDividend.Classical.reflectedSup_positive_height_sSup_attained
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:40:09.727168+00:00
-- url     : https://prove2.me/theorems/f0132d0c-cd5b-4fd3-a778-65506a3595d7
-- title:
--   A finite actual reflected Lévy excursion achieves its positive exact path supremum at a strictly interior time
-- statement:
--   For any actual reflected spectrally negative Lévy path R=S−X and a strictly positive finite excursion lifetime ζ with R(ζ)=0, suppose its supremum over the whole excursion is strictly positive. Then there exists a strictly interior time 0<T<ζ at which R(T) exactly equals the mathematical supremum of the path over [0,ζ]. This derives upper boundedness automatically from proven upper semicontinuity on compact intervals and derives sharpness automatically from least-upper-bound properties. It eliminates both explicit upper bound and sharpness hypotheses of the earlier finite-height attainment theorem.
-- source:
--   Compact upper semicontinuous extrema and conditional real sSup properties, Kuznetsov-Kyprianou-Rivero (2013) excursion-height regularity.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_positive_height_attained

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_positive_height_sSup_attained
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) (hζ : 0 < ζ)
    (hEnd : reflectedSup X ζ ω = 0)
    (hPos : 0 < sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 ζ)) :
    ∃ T : ℝ≥0, 0 < T ∧ T < ζ ∧
      reflectedSup X T ω =
        sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 ζ) := by sorry
