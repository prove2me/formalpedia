-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_adaptive_predictable_signed_generator_tail_vanishes
-- name    : AvramDividend.Classical.avram_wave7_07_original_adaptive_predictable_signed_generator_tail_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:41:05.156364+00:00
-- url     : https://prove2.me/theorems/bc012dc3-4e72-427b-96ca-a97bf785acc5
-- title:
--   Original stopped Lévy nonlinear negative-generator signed drift tends to zero for adaptive predictable shrinking cutoffs
-- statement:
--   For the genuine spectrally negative Lévy sample space, Lévy measure X.ν, right-continuous predictable clock μ and dividend-controlled ruin-stopped surplus, every jointly predictable decreasing family of marked cutoffs tending to empty has a vanishing real signed integrated C2 negative-jump Taylor generator drift after bounded predictable discount. The proof uses the accepted adaptive absolute L1 tail limit, the exact Bochner integral norm versus lintegral norm bound and continuity of ENNReal.toReal at zero. The canonical subtraction z·w'(Y) on -1<z<0 is retained; this controls the compensator drift and does not identify an unproved intrinsic jump-count process.
-- source:
--   W7-07 exact original-source signed generator-drift tail from already Proved adaptive marked absolute L1 tail 89c82c95. Direct finite-horizon source jump drift limit for W7-08; no unknown compensation assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_adaptive_predictable_mark_L1_tail_vanishes
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_adaptive_predictable_signed_generator_tail_vanishes
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
      ∫ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r => a r.1 * HS r) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by sorry
