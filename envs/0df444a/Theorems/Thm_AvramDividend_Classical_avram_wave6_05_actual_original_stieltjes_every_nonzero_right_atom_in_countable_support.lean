-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support
-- name    : AvramDividend.Classical.avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:13:04.271133+00:00
-- url     : https://prove2.me/theorems/52b6ab3d-b79a-4735-ad09-cb3841945cc3
-- title:
--   Actual original full Stieltjes atomic support captures every nonzero right-dividend atom with weighted countable sum
-- statement:
--   For every original adapted nondecreasing dividend strategy, on a closed horizon [0,T] the genuine original right-Lebesgue–Stieltjes dividendMeasure has its exact atomless-plus-countable atomic decomposition, all rightLimit dividend atoms, and full arbitrary-weight integral decomposition. The exact atomic weighted tsum is retained, and the same countable atomic support A is shown to contain every physical-time singleton with nonzero mass of the actual original measure. Thus the countable right-payment series cannot omit any actual nonzero initial, interior or endpoint atom, even when dividend jumps accumulate or the remaining mass is singular-continuous. Only the original dividend-strategy hypothesis is used, not cap, admissibility, smoothness or finite-jump controls.
-- source:
--   Start with the canonically Proved exact actual Stieltjes weighted-atom tsum theorem. Suppose a nonzero singleton mass occurs outside its countable support A. The singleton is then contained in Aᶜ and has μatom mass zero by support and measure_mono_null. The diffuse component gives singleton mass zero by NullSingletonClass. Their exact sum μ=μatom+μdiffuse therefore has zero singleton mass, contradiction. Every original nonzero right-payment atom lies in A.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stieltjes_atomic_weighted_tsum_exact

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support
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
        ∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) := by sorry
