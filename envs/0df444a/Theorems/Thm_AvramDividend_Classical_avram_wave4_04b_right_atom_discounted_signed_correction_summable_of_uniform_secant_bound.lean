-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_right_atom_discounted_signed_correction_summable_of_uniform_secant_bound
-- name    : AvramDividend.Classical.avram_wave4_04b_right_atom_discounted_signed_correction_summable_of_uniform_secant_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:51:14.743628+00:00
-- url     : https://prove2.me/theorems/7b1e4572-3216-4fb9-9d29-ba4de7f82670
-- title:
--   Finite Stieltjes atom mass plus a uniform secant estimate implies convergence of the complete discounted signed payment-jump series
-- statement:
--   For the original adapted Lévy dividend reserve, if the countable actual finite-horizon dividend singleton masses are real summable, the discount q is nonnegative and times are nonnegative, and a uniform secant-magnitude bound holds relative to actual dividend atom mass, the real discounted signed chronological right-payment correction series converges absolutely. The uniform secant bound is a genuine local Lipschitz/domain regularity condition, independent of and stronger than the HJB lower-gradient bound; it is not silently inferred from interior ContDiffOn up to ruin/cap endpoints.
-- source:
--   Mathlib Summable.of_norm_bounded, Real.exp_le_one_iff; actual source dividendMeasure and riskProcess. The mass-summability premise is independently established for source finite horizon by 04-B.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_right_atom_discounted_signed_correction_summable_of_uniform_secant_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (A : Set ℝ) (hA : A.Countable)
    (hAnonneg : ∀ s : A, (0 : ℝ) ≤ (s : ℝ))
    (hq : 0 ≤ q)
    (L : ℝ) (hL : 0 ≤ L)
    (hMass : Summable (fun s : A => (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(s : ℝ)}).toReal))
    (hSecantBound : ∀ s : A, |((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))| ≤ L * (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(s : ℝ)}).toReal) :
    Summable (fun s : A => Real.exp (-(q * (s : ℝ))) * ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))) := by sorry
