-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_discount_thinned_L1_tail_vanishes
-- name    : AvramDividend.Classical.avram_wave7_07_original_predictable_discount_thinned_L1_tail_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:28:02.833094+00:00
-- url     : https://prove2.me/theorems/9fca6b5e-2af5-4216-89b0-edd1c8b7d3e0
-- title:
--   Original stopped Lévy C2 Taylor negative-mark L1 tails vanish with bounded predictable discount and arbitrary mark thinning
-- statement:
--   On the actual spectrally negative Lévy source and right-continuous predictable sigma algebra, for the ruin-stopped C2 nonlinear negative-jump Taylor correction with canonical cutoff -1<z<0 and compact positive-reserve localisation, any jointly predictable mark thinning S and predictable discount in [0,1] preserve vanishing absolute L1 mark energy for any decreasing sequence of mark sets with empty intersection. The measure is the genuine μ ⊗ (X.ν restricted to negative marks) and no intrinsic source jump-count compensator is assumed.
-- source:
--   W7-07 source-faithful discounted L1 small-mark limit from proved discounted original C2 L1/L2 energy 26fe1474, via antitone convergence. Supplies W7-08 compensated source generator tail approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_predictable_discount_thinned_L1_tail_vanishes
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
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ 1)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
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
    let A : ℕ → Set ((ℝ≥0 × Ω) × ℝ) := fun n => {p | p.2 ∈ B n}
    Tendsto (fun n : ℕ =>
      ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        (A n).indicator (fun r =>
          ENNReal.ofReal (|a r.1 * (S.indicator HS r)|)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by sorry
