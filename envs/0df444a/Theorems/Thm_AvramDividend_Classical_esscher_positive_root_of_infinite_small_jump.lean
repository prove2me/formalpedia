-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_of_infinite_small_jump
-- name    : AvramDividend.Classical.esscher_positive_root_of_infinite_small_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:05:36.729724+00:00
-- url     : https://prove2.me/theorems/d2ddf6a2-9103-42ab-9af0-2804d8444841
-- title:
--   Infinite small jumps give a positive Esscher root once the Lévy exponent is continuous at nonnegative parameters
-- statement:
--   For the zero-Gaussian infinite-small-jump-first-moment case, the existing proved Lévy–Khintchine growth theorem gives ψ(θ)>q for all sufficiently large θ. If the canonical ψ is continuous on nonnegative parameters and ψ(0)=0, the pinned intermediate-value theorem then supplies a strictly positive real Esscher root φ with ψ(φ)=q. This closes the root existence step conditional only on the still-to-be-formalised ψ continuity/normalisation facts, not on the excursion-height construction.
-- source:
--   Proved psi_eventually_gt_of_infinite_small_jump_moment and positive_continuous_root_from_growth; source canonical SpectrallyNegativeLevy.ψ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_of_infinite_small_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q : ℝ) (hq : 0 < q)
    (hcont : ContinuousOn X.ψ (Ici (0 : ℝ))) (hzero : X.ψ 0 = 0) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by sorry
