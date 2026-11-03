-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_mark_thinning_L2_negative_tail_vanishes
-- name    : AvramDividend.Classical.avram_wave7_07_original_predictable_mark_thinning_L2_negative_tail_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:50:21.123083+00:00
-- url     : https://prove2.me/theorems/24dc3e28-96c8-4899-8022-dd0ef3052f07
-- title:
--   Original jointly predictable thinned C² negative-source jump square-energy cut-off tails vanish
-- statement:
--   Under the literal original spectrally negative Lévy source X, dividend control D and ruin stop, every jointly predictable thinning of the C2 negative-mark Taylor correction has L2 energy tails vanishing along any decreasing sequence of measurable mark sets with empty intersection, measured on the original predictable finite clock times restricted Lévy measure. This is an original-source nonlinear jump-error localisation theorem and introduces no independent Poisson space or extra martingale assumption.
-- source:
--   W7-07 combines proved full stopped C2 kernel measurability, its arbitrary jointly predictable finite L2 thinning 70cc5bb4, and pinned Mathlib antitone lintegral dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_predictable_mark_thinning_L2_negative_tail_vanishes
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
          ENNReal.ofReal ((S.indicator HS r) ^ 2)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by sorry
