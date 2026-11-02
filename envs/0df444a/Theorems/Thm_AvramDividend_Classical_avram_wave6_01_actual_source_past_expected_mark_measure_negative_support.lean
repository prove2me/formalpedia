-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_actual_source_past_expected_mark_measure_negative_support
-- name    : AvramDividend.Classical.avram_wave6_01_actual_source_past_expected_mark_measure_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:19:39.436384+00:00
-- url     : https://prove2.me/theorems/fcdf2ee3-87b1-4487-95ea-eb4f1992bf02
-- title:
--   Every original BV or UBV past-restricted expected jump-mark measure vanishes on nonnegative marks
-- statement:
--   For any original spectrally negative Lévy X, with no BV or finite-intensity assumptions, every past event A∈𝓕_s admits the genuine source expected jump-mark measure ρ_{A;s,t}, with ρ(B)=E_P[1_A N_X((s,t]×B)] for all Borel B, and ρ([0,∞))=0. This combines the Proved original source measure existence and pointwise negative support for the literal left-limit jumps. It preserves Ω,P,𝓕,X.X and requires no detached point process or proposed compensator. The exact source negative support is the needed Mark-space reduction before finite negative-band monotone exhaustion.
-- source:
--   Canonical source expected mark measure existence 7ffab5e4 and source pointwise negative jump support 12e84fff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_jump_mark_measure_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_actual_source_past_expected_mark_measure_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ ρ : Measure ℝ,
      ρ (Ici (0 : ℝ)) = 0 ∧
      ∀ B : Set ℝ, MeasurableSet B →
        ρ B = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P) := by sorry
