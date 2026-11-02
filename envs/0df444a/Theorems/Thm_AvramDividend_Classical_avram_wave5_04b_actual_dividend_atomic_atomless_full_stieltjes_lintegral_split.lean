-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_actual_dividend_atomic_atomless_full_stieltjes_lintegral_split
-- name    : AvramDividend.Classical.avram_wave5_04b_actual_dividend_atomic_atomless_full_stieltjes_lintegral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:41:47.529176+00:00
-- url     : https://prove2.me/theorems/864aec7f-f10f-4338-b68a-26a5d4022c3a
-- title:
--   Exact arbitrary-weight full Stieltjes dividend integral decomposition into countable right atoms and diffuse/singular-continuous variation
-- statement:
--   On each original source sample path and finite horizon, the genuine right-Stieltjes dividendMeasure restricts to a countable right-atomic measure plus an atomless remainder. For every arbitrary nonnegative extended-real weight, its full lower integral equals exactly the sum of the atomic and atomless lower integrals. The atom formula includes D_{0+}-D_0 at time zero. The atomless term includes absolutely continuous and singular-continuous dividend variation without assuming a dividend density or reserve-interior occupation.
-- source:
--   Reuse Proved canonical actual measure countable atoms/atomless decomposition a4bdfc6a-e9ea-441d-a535-c9160a08691b and pinned Mathlib MeasureTheory.lintegral_add_measure. Does not require deriv w or strict hloc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_actual_dividend_atomic_atomless_full_stieltjes_lintegral_split
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
      (∫⁻ s, f s ∂μ) =
        (∫⁻ s, f s ∂μatom) + (∫⁻ s, f s ∂μdiffuse) := by sorry
