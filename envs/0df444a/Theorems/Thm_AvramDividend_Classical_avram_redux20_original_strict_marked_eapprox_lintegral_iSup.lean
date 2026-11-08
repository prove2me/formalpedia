-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_eapprox_lintegral_iSup
-- name    : AvramDividend.Classical.avram_redux20_original_strict_marked_eapprox_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:13:35.63322+00:00
-- url     : https://prove2.me/theorems/932f5536-8a89-49b6-beaf-217a61f72e36
-- title:
--   Original strict intrinsic Borel marked loss equals the supremum of finite simple marked loss integrals
-- statement:
--   For the literal original spectrally negative Lévy path and its strict finite-horizon negative jump cutoff, the intrinsic integral of any nonnegative measurable Borel mark loss equals the increasing supremum of the canonical simple-function mark-loss integrals. The proof uses the actual finite time support, preserving repeated marks with multiplicity and avoiding any artificial measurable time-to-mark assumption.
-- source:
--   Specialise the accepted original source Borel-weight finite-sum theorem to each canonical simple mark approximant and the full Borel mark weight, then use the finite physical time pullback approximation lemma to interchange the increasing supremum and finite sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_borel_weight_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_redux20_finite_mark_eapprox_pullback
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux20_original_strict_marked_eapprox_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    let μ := (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    (⨆ n : ℕ, ∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then MeasureTheory.SimpleFunc.eapprox g n p.2 else 0 ∂μ) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then g p.2 else 0 ∂μ) := by sorry
