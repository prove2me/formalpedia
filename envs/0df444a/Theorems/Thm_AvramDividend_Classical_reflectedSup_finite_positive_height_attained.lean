-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_positive_height_attained
-- name    : AvramDividend.Classical.reflectedSup_finite_positive_height_attained
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:57:28.373467+00:00
-- url     : https://prove2.me/theorems/a4781d5a-7a97-4a15-86b1-cdd0055a0a85
-- title:
--   Positive maximum of an actual finite reflected Lévy excursion is attained strictly before its lifetime
-- statement:
--   For a spectrally negative Lévy sample path, suppose the reflected drawdown R_t reaches a positive sharp upper bound x during an excursion with finite lifetime ζ>0, and R_ζ=0. The actual reflected process starts at zero and is upper semicontinuous on [0,ζ] by the separately proved càdlàg/no-negative-jumps path results. Compact maximum attainment then ensures a time 0<T<ζ with R_T=x. This discharges the height-hitting part of the excursion-height atomlessness argument for finite-lifetime excursions, without assuming the maximum is attained at the outset. It does not address infinite-lifetime excursions.
-- source:
--   Kuznetsov–Kyprianou–Rivero 2013, Section 2.3 excursion-height atomlessness, and accepted finite-excursion upper-semicontinuous maximum attainment.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_origin_eq_zero
import Theorems.Thm_AvramDividend_Classical_finite_excursion_height_attained_of_upperSemicontinuous

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_finite_positive_height_attained
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) (hζ : 0 < ζ)
    (hEnd : reflectedSup X ζ ω = 0)
    (x : ℝ) (hx : 0 < x)
    (hBound : ∀ t : ℝ≥0, t ≤ ζ → reflectedSup X t ω ≤ x)
    (hSharp : ∀ y : ℝ, y < x →
      ∃ t : ℝ≥0, t ≤ ζ ∧ y < reflectedSup X t ω) :
    ∃ T : ℝ≥0, 0 < T ∧ T < ζ ∧ reflectedSup X T ω = x := by sorry
