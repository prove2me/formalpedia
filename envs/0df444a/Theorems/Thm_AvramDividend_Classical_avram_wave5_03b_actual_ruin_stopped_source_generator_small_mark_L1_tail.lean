-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_small_mark_L1_tail
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_generator_small_mark_L1_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:33:31.632875+00:00
-- url     : https://prove2.me/theorems/a5fe4f03-2159-444c-bce0-a39e705f2ee0
-- title:
--   Actual controlled ruin-stopped Lévy generator Taylor drift has vanishing absolute L1 intensity on shrinking negative mark bands
-- statement:
--   For the original spectrally negative Lévy source and adapted dividend control, the genuine prepayment reserve Taylor remainder with inclusive ruin stopping has vanishing absolute L1 source-compensator intensity on every decreasing measurable family of sufficiently small negative mark sets with empty intersection. The small-mark radius exists from the proved interior C2 quadratic generator bound, and the result uses only the source Lévy measure integrability with finite predictable time-sample measure. It is a source-coupled drift-tail limit, not a martingale or unproved compensator identity.
-- source:
--   Proved 03-B source generator near C2 envelope 9b510aa0-fdb5-447f-a79d-823d7328cbcc plus Levy quadratic mark integrability and P1 decreasing energy tail 03134e86-e6de-49ec-8d59-26afc753df00. Retains actual Y = leftLim (x + X.X - rightLimit D), survival t<=ruinTime X x D, truncation z>-1, X.nu, finite predictable right-continuous μ; does not assume source independence from D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_generator_small_mark_L1_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u + δ) (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
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
    ∃ r : ℝ, 0 < r ∧
      ∀ (B : ℕ → Set ℝ)
        (hBm : ∀ n, MeasurableSet (B n))
        (hBnear : ∀ n, B n ⊆ Ioo (-r) 0)
        (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) = 0 := by sorry
