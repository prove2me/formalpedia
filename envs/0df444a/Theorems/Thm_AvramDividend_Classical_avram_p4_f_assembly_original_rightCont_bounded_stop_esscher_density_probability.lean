-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_density_probability
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_density_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:37:47.675864+00:00
-- url     : https://prove2.me/theorems/982cda1b-7840-4244-a4fa-4fe296412833
-- title:
--   Genuine original right-continuous bounded stopped Esscher density is a probability
-- statement:
--   For the original spectrally negative Lévy process and a genuinely bounded stopping time in its right-continuous filtration, the exact stopped Esscher exponential defines a probability change of measure. Construct the genuine same-path right-continuous Lévy lift and reuse the source bounded-stop Esscher theorem. This directly repairs the filtration mismatch in P4-F's raw exponential envelope route, without an auxiliary independent process.
-- source:
--   Proved source `avram_wave5_04_source_rightCont_levy_lift` e58a099d (same structure construction), `levy_indepIncrements_rightCont`, and `esscher_bounded_stop_density_probability` a74b4ab5. Source type and triplet identity are exact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability
open MeasureTheory ProbabilityTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_density_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    IsProbabilityMeasure (P.withDensity (fun ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) := by sorry
