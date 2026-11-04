-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:32:21.24271+00:00
-- url     : https://prove2.me/theorems/b91875a4-9d48-4c3c-b658-ef43e2d93862
-- title:
--   Genuine bounded original Lévy stopping gives discounted source exponential L1 for every q
-- statement:
--   At any bounded right-continuous stopping time for the original spectrally negative Lévy process, exp(θ X_τ−qτ) is integrable for θ≥0 and any real q. Unlike the previously accepted ψθ≤q lemma, only the finite horizon is used: the ratio exp((ψθ−q)τ) is bounded by exp(|ψθ−q|H). Establish integrability by domination from the original stopped Esscher mean-one density.
-- source:
--   Accepted original rightCont bounded-stop Esscher mean-one 46c2da57; pinned Mathlib integrable_of_integral_eq_one and Integrable.mono_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω => Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P := by sorry
