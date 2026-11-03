-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_discount_thinned_L2_tail_vanishes
-- name    : AvramDividend.Classical.avram_wave7_07_original_predictable_discount_thinned_L2_tail_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:27:12.980204+00:00
-- url     : https://prove2.me/theorems/2c1223fc-632d-4e94-993a-6cf6657dfad1
-- title:
--   Original stopped spectrally negative Lévy C2 Taylor small-mark L2 tails vanish with bounded predictable discount and mark thinning
-- statement:
--   In the original spectrally negative Lévy probability space, process, filtration, true predictable clock and dividend strategy, localise the ruin-stopped nonlinear C2 Taylor kernel on a compact positive-reserve interval. For any jointly predictable negative-mark selection S, any predictable discount 0≤a≤1, and any measurable decreasing sequence of shrinking mark sets with empty intersection, the quadratic energy of the predictably discounted and thinned kernel tends to zero on the actual product measure μ ⊗ X.ν|(-∞,0). The statement preserves the source truncation -1<z<0 and does not assume or claim an intrinsic jump-count compensator.
-- source:
--   W7-07 source-faithful discounted small-jump L2 tail from proved bounded predictable discount L1/L2 energy 26fe1474 and original marked Lévy σ-finite measure, via antitone convergence. Supplies W7-06 martingale approximants and W7-08 finite-horizon source jump part.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_predictable_discount_thinned_L2_tail_vanishes
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
          ENNReal.ofReal ((a r.1 * (S.indicator HS r)) ^ 2)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by sorry
