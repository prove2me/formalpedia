-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_adaptive_predictable_mark_L2_tail_vanishes
-- name    : AvramDividend.Classical.avram_wave7_07_original_adaptive_predictable_mark_L2_tail_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:30:01.482302+00:00
-- url     : https://prove2.me/theorems/8d0d4823-ef9f-4c77-8e9e-25ae7330f555
-- title:
--   Source Lévy stopped C2 Taylor L2 energy vanishes under time-state-adaptive decreasing predictable marked cutoffs
-- statement:
--   In the exact spectrally negative Lévy source and original dividend reserve, any sequence of jointly predictable mark sets decreasing to empty, even when cutoffs depend on time and path, has vanishing L2 energy for the ruin-stopped compactly localised nonlinear C2 negative-jump Taylor correction weighted by a predictable discount in [0,1]. Integration is against the genuine source predictable finite clock μ times X.ν on negative marks. It uses the canonical -1<z<0 truncation and requires no replacement Poisson space or unproved source jump-count compensator.
-- source:
--   W7-07 original-source adaptive predictable cutoffs, antitone lintegral convergence from proved 26fe1474 full weighted L2 energy. A source-filtration approximant interface for W7-06/W7-08 with path-adaptive marked truncations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_adaptive_predictable_mark_L2_tail_vanishes
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
    (S : ℕ → Set ((ℝ≥0 × Ω) × ℝ))
    (hSm : ∀ n, MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] (S n))
    (hSanti : Antitone S) (hSempty : (⋂ n, S n) = ∅)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ 1) :
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
    Tendsto (fun n : ℕ =>
      ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r =>
          ENNReal.ofReal ((a r.1 * HS r) ^ 2)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by sorry
