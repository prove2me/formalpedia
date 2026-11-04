-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_integrable
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:17:13.551534+00:00
-- url     : https://prove2.me/theorems/00c43baf-21b8-4820-b682-c708db9b6b92
-- title:
--   Genuine bounded stopped original discounted Lévy exponential is integrable under measurable clock and q at least psi
-- statement:
--   On the original Lévy sample space with the actual right-continuous bounded stopping-time hypothesis and real-measurable stopped clock, the discounted exponential e^(θ Xτ - qτ) is L1 whenever θ≥0 and ψ(θ)≤q. The proved original stopped Esscher mean one gives an integrable dominating e^(θXτ-ψθτ); measurability of τ supplies the multiplicative discount factor; use L1 dominated integrability. These exact measurability and stopping hypotheses occur in canonical P4-F.
-- source:
--   Proved P4-F original rightCont bounded Esscher likelihood mean one 46c2da57; pinned Mathlib integrable_of_integral_eq_one, AEStronglyMeasurable.fun_mul, Integrable.mono'.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω => Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P := by sorry
