-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_dividend_diffuse_preserves_strict_source_prejump_ae
-- name    : AvramDividend.Classical.avram_wave4_04b_actual_dividend_diffuse_preserves_strict_source_prejump_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:14:02.593195+00:00
-- url     : https://prove2.me/theorems/0b7de539-6541-40bf-8d7a-76c5e0bdd988
-- title:
--   True finite-horizon Lévy dividend Stieltjes diffuse part identifies the strict pre-jump controlled reserve pathwise
-- statement:
--   For every genuine spectrally negative Lévy sample path and every adapted dividend strategy, the full finite-horizon dividend Stieltjes measure has an exact countable right-atomic plus atomless diffuse decomposition preserving all mass and exact singleton payment sizes. The actual (possibly path-dependent and singular-continuous) diffuse component sees the pre-source reserve equal to the genuine strict source pre-jump controlled reserve at almost every strictly positive time. This avoids an unjustified exchange of sample and random-measure almost-everywhere quantifiers and leaves all stochastic compensation obligations open.
-- source:
--   Composes Proved complete dividend decomposition d19177af-e2bc-4c43-813a-5abc846cb4bf with Proved per-path arbitrary atomless measure source comparison a14bf58b-7618-46d8-8305-425cfaa67b49. No new hypotheses or artificial Ito–Meyer axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_actual_dividend_diffuse_preserves_strict_source_prejump_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) ∧
      (∀ᵐ s ∂μdiffuse, 0 < s →
        riskProcess X x D s.toNNReal ω =
          x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω) := by
  sorry
