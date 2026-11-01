-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_original_controlled_negative_mark_tail_energy_inf_zero
-- name    : AvramDividend.Classical.avram_wave4_04_original_controlled_negative_mark_tail_energy_inf_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:26:17.586194+00:00
-- url     : https://prove2.me/theorems/92c7080f-090c-4f53-8553-012bee0b5375
-- title:
--   Controlled original Lévy jump-kernel quadratic energy vanishes on shrinking negative-mark regions
-- statement:
--   For the actual source Lévy X and the same adapted dividend control D, any compactly clipped predictable left-limit reserve jump kernel has vanishing finite-horizon squared energy on every antitone sequence of measurable negative-mark sets with empty intersection. The observation measure μ is an arbitrary finite measure on the original predictable sigma algebra. The proof composes the uniform original-strip quadratic budget, X.ν_integrable and the Proved general marked-energy tail iInf theorem. This is the exact analytic L2 Cauchy tail needed once an independent same-source compensated jump isometry is proved, and does not assert that the count measure or martingale is already available.
-- source:
--   Source-faithful daughter of corrected UBV primary 429e17ca-5528-40b5-b593-7c03973d0706; exact uniform original-source mark strip budget child 246dcd6f-e5ff-4737-a3e2-75f31f5e0f4d and P1 generic source square-energy tail 03134e86-e6de-49ec-8d59-26afc753df00. No same-law substitution and no uncorrected ∫|z|ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_original_controlled_negative_strip_quadratic_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_original_controlled_negative_mark_tail_energy_inf_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) = 0 := by sorry
