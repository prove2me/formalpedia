-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_signed_jump_pos_neg_count
-- name    : AvramDividend.Classical.avram_p3_2_original_stopped_signed_jump_pos_neg_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:28:56.294262+00:00
-- url     : https://prove2.me/theorems/1ee67fd9-a051-4739-847b-b69e196a4d90
-- title:
--   Stopped original Lévy signed positive and negative jump counting identities
-- statement:
--   The exact original spectrally negative Lévy marked jump counting measure, filtered by an arbitrary measurable physical stopped-time region, has signed positive and negative ENNReal parts equal to the corresponding true source jump tsums. Both retain the zero-time exclusion, the actual X jumps and both signs of the kernel, preparing predictable compensation without assuming finite activity.
-- source:
--   Pinned accepted original nonlinear marked-count theorem 008c9b37, measurable stopped indicators and positive/negative ENNReal.ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_source_nonlinear_jump_count_eq_tsum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_stopped_signed_jump_pos_neg_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    [DecidablePred (fun u : ℝ≥0 => u ∈ S)]
    (F : ℝ≥0 × ℝ → ℝ) (hF : Measurable F) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ((∫⁻ p, (if p.1 ∈ S then ENNReal.ofReal (F p) else 0) ∂NX) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
            ∧ u ∈ S then
          ENNReal.ofReal (F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        else 0) ∧
    ((∫⁻ p, (if p.1 ∈ S then ENNReal.ofReal (-F p) else 0) ∂NX) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
            ∧ u ∈ S then
          ENNReal.ofReal (-F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        else 0) := by sorry
