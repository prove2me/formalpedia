-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_weight_generator_negative_mark_L1_tail
-- name    : AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_weight_generator_negative_mark_L1_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:13:30.27404+00:00
-- url     : https://prove2.me/theorems/4395ea15-12af-49b8-9c9d-09544cbdf3b9
-- title:
--   Signed predictable unit-contraction original stopped generator drift loses no negative-mark L¹ mass
-- statement:
--   For the original X.X prepayment left-limit controlled reserve and exact inclusive ruinTime, the original SpectrallyNegativeLevy.generatorIntegrand full negative real Lévy-mark compensator has vanishing physical L1 drift tail under any possibly signed 𝓕.rightCont predictable multiplier a with |a|≤1, on any antitone measurable negative mark bands shrinking to the empty set. Deduce this from the already Proved source-specific positive predictable weight tail theorem a5242e78 by passing to |a|; norm invariance removes the sign. This is physical generator-intensity compensation, not an assertion of the still-open original actual source jump-count hFuture law.
-- source:
--   Wave6 Chat04 signed original-source generator mark L1 drift tail from Proved a5242e78, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_weight_generator_negative_mark_L1_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (a : (ℝ≥0 × Ω) → ℝ)
    (ha : Measurable[𝓕.rightCont.predictable] a)
    (haBound : ∀ p, |a p| ≤ (1 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖a p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
      atTop (𝓝 0) := by sorry
