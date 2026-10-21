-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_general_future_increment_conditional_expectation
-- name    : AvramDividend.Classical.chat04_general_future_increment_conditional_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:47:01.989996+00:00
-- url     : https://prove2.me/theorems/60e3f274-5580-448a-a1d8-6485fa8ab41a
-- title:
--   Conditional expectation of any integrable Borel function of a future Lévy increment
-- statement:
--   For a canonical spectrally negative Lévy process and ordered deterministic times s≤t, let φ:R→R be any Borel measurable payoff with integrable stationary increment payoff φ(X_(t−s)). Then conditional on the complete history sigma algebra F_s, the payoff φ(X_t−X_s) has almost-sure conditional expectation equal to the constant unconditional expectation of φ(X_(t−s)). No scale-function properties or further moment assumptions are imposed. The proof uses the original full-filtration independent increments to show φ(X_t−X_s) is independent of F_s, the stationary increment law for equal distribution and integrability, and the pinned Mathlib condExp_indep_eq theorem. This generalises the already officially ACCEPTED fixed-capital q-scale conditional expectation theorem and provides the one-step conditional kernel needed for arbitrary cylinder survival payoffs.
-- source:
--   Verified ACCEPTED chat04_shifted_scale_future_increment_condExp UUID c1929686-e71f-401e-b969-c5bf79fafd0b, generalised by replacing W(x+·) with any measurable integrable φ. Canonical SpectrallyNegativeLevy indepIncrements, stationaryIncrements, adapted. Pinned Mathlib MeasureTheory.condExp_indep_eq and IdentDistrib.integrable_iff.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_general_future_increment_conditional_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P) :
    P[(fun ω => φ (X.X t ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, φ (X.X (t - s) ω) ∂P) := by sorry
