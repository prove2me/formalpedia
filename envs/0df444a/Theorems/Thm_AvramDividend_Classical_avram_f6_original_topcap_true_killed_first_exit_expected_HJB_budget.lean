-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_true_killed_first_exit_expected_HJB_budget
-- name    : AvramDividend.Classical.avram_f6_original_topcap_true_killed_first_exit_expected_HJB_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:08:33.189337+00:00
-- url     : https://prove2.me/theorems/9dbe8433-2987-4c67-b9af-45cd3df5aba8
-- title:
--   Original topcap HJB candidate stopped killed two-sided first-exit expected supermartingale budget
-- statement:
--   For original standing UBV spectrally negative Lévy, actual topcap HJB generator and gradient candidate w, the true source stopped discounted killed upper-exit expectation from initial reserve 1 obeys w(b) E[e^{-q τ_b}; τ_b<τ^-_0]≤w(1) for every b≥1. Prove through original stopped Itô-Meyer, genuine compensated jump mean zero and optional stopping; no assumed martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_topcap_true_killed_first_exit_expected_HJB_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0)) (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∀ b : ℝ, 1 ≤ b →
      w b * (twoSidedExitExpectation X q b 1).toReal ≤ w 1 := by sorry
