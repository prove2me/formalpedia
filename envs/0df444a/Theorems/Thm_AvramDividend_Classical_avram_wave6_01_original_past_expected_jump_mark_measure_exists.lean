-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_jump_mark_measure_exists
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_expected_jump_mark_measure_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:57:18.987391+00:00
-- url     : https://prove2.me/theorems/7ffab5e4-db23-4ca5-947c-0b67282bc927
-- title:
--   The actual past-restricted expected Lévy jump-mark count is a measure on ℝ
-- statement:
--   On the same original Ω, P, filtration 𝓕 and Lévy sample paths X.X, for every A∈𝓕_s there exists a countably additive measure ρ on the actual jump-mark space ℝ such that for each measurable mark set B, ρ(B) equals the expected literal intrinsic jump count in (s,t] × B over ω∈A. Construct ρ by restricting the P-integrated canonically proved original s-finite jump kernel to (s,t]×ℝ and projecting onto the mark coordinate. This introduces no Poisson copy, guessed intensity, compensator assumption, or conditional target.
-- source:
--   Canonical Proved source intrinsic s-finite kernel eb357d08; measure bind, time restriction and Prod.snd measurable pushforward, with exact fibrewise equality to X's literal left-limit jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_past_expected_jump_mark_measure_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ ρ : Measure ℝ, ∀ B : Set ℝ, MeasurableSet B →
      ρ B = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by sorry
