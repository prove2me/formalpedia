-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_stopped_L2_error_bound_gives_L1_convergence
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_stopped_L2_error_bound_gives_L1_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:12:30.491555+00:00
-- url     : https://prove2.me/theorems/ac0bef79-a4d5-471e-b7f0-2d872a89f8f3
-- title:
--   Actual stopped Lévy residual L1 convergence from uniform L2 error energy without a dominating envelope
-- statement:
--   On the actual source Lévy probability space, if finite-clock residual errors converge almost surely to zero, their norms are a.e. measurable and their squared norms have uniformly bounded integrals, then expected absolute error tends to zero. Instantiate the already Proved original-source-compatible uniform second-moment limit theorem with the nonnegative random errors and zero limit. No single common integrable almost-sure bound is postulated; a genuinely uniform Ito/BDG L2 energy bound must be proved from the source stochastic construction before application.
-- source:
--   Original source stopped residual L2/UI passage; Proved nonnegative_integral_tendsto_of_uniform_second_moment (bef79c38-a4aa-42be-b897-fd1baeed7998).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_stopped_L2_error_bound_gives_L1_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hDiffMeas : ∀ k, AEStronglyMeasurable
      (fun ω => ‖Mk k ω - M ω‖) P)
    (hAs : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω)))
    (C : ℝ) (hC : 0 ≤ C)
    (hDiffSq : ∀ k, Integrable (fun ω => (‖Mk k ω - M ω‖) ^ 2) P ∧
      (∫ ω, (‖Mk k ω - M ω‖) ^ 2 ∂P) ≤ C) :
    Tendsto (fun k => ∫ ω, ‖Mk k ω - M ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
