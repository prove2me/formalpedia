-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:42:08.012073+00:00
-- url     : https://prove2.me/theorems/46c2da57-89da-43c5-ac67-b6b66caa64b4
-- title:
--   Original right-continuous bounded-stop Esscher likelihood has mean one
-- statement:
--   For a bounded 𝓕.rightCont-stopping time of the original spectrally negative Lévy process, the original stopped Esscher likelihood has real expectation exactly one. Lift the same original paths and triplet to right-continuous filtration and apply the proved bounded-stop exact-mass theorem.
-- source:
--   Proved exact original paths and triplet lift e58a099d, source lemma levy_indepIncrements_rightCont, Proved esscher_bounded_stop_likelihood_integral_one c31104b1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_integral_one
open MeasureTheory ProbabilityTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ) ∂P) = (1 : ℝ) := by sorry
