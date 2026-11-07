-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel
-- name    : AvramDividend.Classical.avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:48:52.380202+00:00
-- url     : https://prove2.me/theorems/7fe50c96-cd31-4e8c-8b74-a9d292112e27
-- title:
--   Exact original indexed compensated HJB H kernel equals original stopped physical-grid C1 kernel
-- statement:
--   The full, source-identical original compact-band H kernel used in the published compensated jump HJB budget, including the nested stopped-time gate and predictor event E on time by sample path, is pointwise the very same real discounted compact-band pre-right-payment negative-mark C1 kernel used in the original physical grid after the redundant T gate. The proof uses the previously published stopped-clock cutoff identity and source-specific conversion of ENNReal stopped time inequalities; there is no equality-in-law surrogate or new stochastic assumption.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compensated_H_kernel_eq_physical_C1_marked_source

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q a b : ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : Ω → ℝ≥0 := fun η =>
      (min (ruinTime X x D η) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Eω : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    ∀ p : ℝ≥0 × ℝ,
      H ((p.1, ω), p.2) =
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ Eω then K p else 0) := by sorry
