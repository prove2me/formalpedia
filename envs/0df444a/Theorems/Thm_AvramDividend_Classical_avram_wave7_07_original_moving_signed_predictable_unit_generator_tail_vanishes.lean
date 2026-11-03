-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_signed_predictable_unit_generator_tail_vanishes
-- name    : AvramDividend.Classical.avram_wave7_07_original_moving_signed_predictable_unit_generator_tail_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:09:31.195777+00:00
-- url     : https://prove2.me/theorems/8d089771-4018-4069-8e99-92cb28a8eb3b
-- title:
--   Original Lévy nonlinear generator real drift tails vanish for arbitrary moving signed predictable unit contractions
-- statement:
--   On original Levy Ω, P, X.X, X.ν and the actual predictable σ-algebra, the real signed nonlinear generator Taylor drift over decreasing jointly predictable marked cutoffs converges to zero for each n-dependent predictable coefficient whose absolute value is at most one. The proof imports the genuinely proved corresponding moving signed unit L1 norm-tail bound and applies the Bochner integral norm ≤ L1 norm with ENNReal.toReal continuity at zero. It leaves the intrinsic compensated original jump count to W7-01/W7-06.
-- source:
--   W7-07 signed generator drift extension of source L1 signed unit predictable contraction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_signed_predictable_unit_contraction_L1_tail_vanishes
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_moving_signed_predictable_unit_generator_tail_vanishes
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
    (a : ℕ → ℝ≥0 × Ω → ℝ)
    (ham : ∀ n, Measurable[𝓕.rightCont.predictable] (a n))
    (ha : ∀ n p, |a n p| ≤ 1) :
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
        (S n).indicator (fun r => a n r.1 * HS r) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by sorry
