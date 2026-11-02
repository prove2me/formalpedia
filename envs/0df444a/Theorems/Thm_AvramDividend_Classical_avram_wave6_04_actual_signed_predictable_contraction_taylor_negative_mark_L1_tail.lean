-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L1_tail
-- name    : AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L1_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:12:17.279282+00:00
-- url     : https://prove2.me/theorems/9901067b-7419-4bda-90be-e456d2ac4ae6
-- title:
--   Any signed predictable unit contraction preserves actual ruin-stopped C² negative Taylor mark L¹ tails
-- statement:
--   For the original X.X, X.ν, adapted dividend D, prepayment left-limit surplus, actual inclusive ruinTime, interior C² test w with zero negative extension, any possibly signed right-continuous predictable scalar a with |a|≤1 preserves vanishing absolute source-Taylor negative-mark compensator L1 mass over arbitrary shrinking measurable negative mark sets. This strengthens the positive random-discount case to signed predictable localisers, without finite first moment of large negative source marks or any assumption that a generic predictable time clock is an actual source jump compensator. The proof is a direct domination of the Proved original full-negative C² mark-tail theorem 19668eea.
-- source:
--   Wave6 Chat04 arbitrary signed predictable contraction full source negative Taylor L1 band tail, direct Proved 19668eea, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L1_tail
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (a : (ℝ≥0 × Ω) → ℝ)
    (ha : Measurable[𝓕.rightCont.predictable] a)
    (haBound : ∀ p, |a p| ≤ (1 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    ∀ (B : ℕ → Set ℝ)
      (hBm : ∀ n, MeasurableSet (B n))
      (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
      (hBanti : Antitone B)
      (hBempty : (⋂ n, B n) = ∅),
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|a p * HS (p,z)|) ∂X.ν ∂μ) = 0 := by sorry
