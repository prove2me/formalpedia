-- Prove2me | Theorems.Thm_AvramDividend_Classical_projective_martingale_early_events_fixed_terminal_law
-- name    : AvramDividend.Classical.projective_martingale_early_events_fixed_terminal_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:03:10.4452+00:00
-- url     : https://prove2.me/theorems/b65a2a53-aa4d-4af9-a903-3ee3724739a3
-- title:
--   Projective martingale event identities transfer to one fixed terminal measure
-- statement:
--   Given a consistent family of probability or finite measures Q_t on a common filtered measurable space and a strongly adapted family of real rewards Z_t satisfying projective martingale earlier-event integral identities between Q_s and Q_t, then for s≤t≤T the earlier-event conditional martingale integral identity holds under the single fixed measure Q_T. This is the rigorous bridge from genuine finite Esscher laws to finite-grid Doob maximal inequalities, without ever asserting the existence of an infinite-horizon tilted probability measure.
-- source:
--   Use the separately proved `setIntegral_eq_of_measures_agree_on_subsigma` for the earlier observable Z_s between Q_s and Q_T, and for Z_t between Q_t and Q_T; in between apply the assumed projective martingale equality. The filtration's monotonicity supplies A∈F_t from A∈F_s. No integration under a different σ-algebra or global tilted law is introduced.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_setIntegral_eq_of_measures_agree_on_subsigma
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.projective_martingale_early_events_fixed_terminal_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Q : ℝ≥0 → Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ)
    (hQ : ∀ s t : ℝ≥0, s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (𝓕 s) A → Q s A = Q t A)
    (hZ : ∀ s t : ℝ≥0, s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (𝓕 s) A →
        (∫ ω in A, Z s ω ∂Q s) = (∫ ω in A, Z t ω ∂Q t))
    (hadapt : ∀ t : ℝ≥0, StronglyMeasurable[𝓕 t] (Z t))
    (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (∫ ω in A, Z s ω ∂Q T) =
    (∫ ω in A, Z t ω ∂Q T) := by sorry
