-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stieltjes_atomic_weighted_tsum_exact
-- name    : AvramDividend.Classical.avram_wave6_05_actual_original_stieltjes_atomic_weighted_tsum_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:04:03.118713+00:00
-- url     : https://prove2.me/theorems/dee892be-f14f-4afd-9aa7-f2f6783cbdff
-- title:
--   Exact genuine original dividend Stieltjes weighted atomic tsum with unchanged diffuse and singular-continuous remainder
-- statement:
--   For any actual adapted nondecreasing dividend strategy and any finite horizon [0,T], the original right-payment Lebesgue–Stieltjes dividendMeasure restricted to that closed horizon admits the countable atomic and atomless decomposition with all exact rightLimit D minus D atoms. For every arbitrary ENNReal weight f, the complete original integral is the sum of atomic and diffuse lower integrals, and the atomic lower integral is exactly the unrestricted countable sum of f(t) times the actual original measure mass at t. This includes t=0 and t=T, allows infinitely many jumps, and leaves the entire absolutely continuous and singular-continuous component intact without imposing finite-jump/smooth-dividend controls. It provides the exact conversion between the original Stieltjes integral and the chronological payment jump series needed by the controlled Ito–Meyer formula.
-- source:
--   Use the canonically Proved original Stieltjes atomic/atomless decomposition and arbitrary-weight lintegral split. Rewrite μatom as Measure.sum of right-atom-weighted Dirac measures. Apply pinned MeasureTheory.lintegral_sum_measure, lintegral_smul_measure and lintegral_dirac, then the ENNReal smul-equals-multiplication identity. No replacement of the original measure is made.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_actual_dividend_atomic_atomless_full_stieltjes_lintegral_split

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_actual_original_stieltjes_atomic_weighted_tsum_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
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
      ((∫⁻ s, f s ∂μ) =
        (∫⁻ s, f s ∂μatom) + (∫⁻ s, f s ∂μdiffuse)) ∧
      ((∫⁻ s, f s ∂μatom) =
        ∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) := by sorry
