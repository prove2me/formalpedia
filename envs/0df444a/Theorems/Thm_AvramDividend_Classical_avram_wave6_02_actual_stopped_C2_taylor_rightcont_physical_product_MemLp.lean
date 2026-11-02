-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_MemLp
-- name    : AvramDividend.Classical.avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_MemLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:27:03.976202+00:00
-- url     : https://prove2.me/theorems/2698107c-21da-4eaf-88cb-697fdf462ff8
-- title:
--   Actual controlled ruin-stopped C² Taylor kernel lies in original predictable product L²
-- statement:
--   The literal inclusive ruin-stopped negative-jump C² Taylor kernel of SpectrallyNegativeLevy X and original adapted dividend control D is a genuine MemLp 2 function on the original right-continuous predictable time-probability space times the original negative-jump Lévy mark measure. Derives product square energy, converts to eNorm energy and applies Mathlib's eLpNorm criterion, without assuming finite first moment of small jumps. This supplies the source-exact MemLp input required by a compensated source L² isometry-to-tail theorem.
-- source:
--   Actual stopped kernel measurable 0e0663b1, actual product energy 2d67e34c, normalized eNorm energy d361e4c4, pinned Mathlib eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_real_product_L2_square_to_eNorm_energy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_MemLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
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
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      MemLp HS (2 : ℝ≥0∞)
        (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
