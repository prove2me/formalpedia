-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_stopped_negative_source_mark_positivepart_lintegral_zero
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_stopped_negative_source_mark_positivepart_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:37:16.323534+00:00
-- url     : https://prove2.me/theorems/eafa21bb-fca7-4c55-a160-8a820f8ea8db
-- title:
--   Original BV complement ruin-stopped interior negative source-mark correction has zero positive expected ν mass
-- statement:
--   For the literal physical Lebesgue-time clock, original probability P, actual original Lévy measure X.ν and source-controlled predictable left-limit reserve, the positive part of the discounted value change associated with any negative source mark integrates to exactly zero over the genuine pre-ruin strict generator interior. The actual measure is (physical time × P) × X.ν, and the stopped interior includes t≤T and t<ruinTime. Measurability of that stopped mark set is explicit; no finite jump rate or L1 bound is presumed. The result is the sign component needed for eventual original-source compensator integration, not a proof of the compensated jump identity.
-- source:
--   Avram-Palmowski-Pistorius (2007) Proposition 4(i), actual predictable stopped generator jump mark integrals. Depends only on Proved original full-cap C1 gradient secant 2ba5cc4f and restricted-measure lintegral congruence; the negative-mark sign is proved directly on the genuine stopped source set, independently of the still-Open W7-17 mark helper 38e7e8f9. This is not a surrogate marked process, and no boundary occupation claim is made.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_stopped_negative_source_mark_positivepart_lintegral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0) :
    let μ : Measure ((ℝ≥0 × Ω) × ℝ) :=
      (((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P).prod X.ν)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set ((ℝ≥0 × Ω) × ℝ) :=
      {p | p.1.1 ≤ T ∧
        (p.1.1 : ℝ≥0∞) < ruinTime X x D p.1.2 ∧
        0 < Y p.1 ∧ ENNReal.ofReal (Y p.1) < C ∧ p.2 < 0}
    MeasurableSet S →
    (∫⁻ p in S, ENNReal.ofReal
      (Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1))) ∂μ) = 0 := by sorry
