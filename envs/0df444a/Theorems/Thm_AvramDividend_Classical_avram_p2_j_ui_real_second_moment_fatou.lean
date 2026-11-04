-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_real_second_moment_fatou
-- name    : AvramDividend.Classical.avram_p2_j_ui_real_second_moment_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:31:33.154724+00:00
-- url     : https://prove2.me/theorems/32d49d29-12b2-4b03-ae14-62e2620ab473
-- title:
--   Fatou inheritance of finite real second moments under almost-everywhere convergence
-- statement:
--   For measurable real functions whose squares have uniformly bounded genuine integrals, their almost-everywhere limit has an integrable square, with second moment no greater than the same bound. A direct Fatou lemma proof works on an arbitrary measure space and makes no source-specific process assumption.

import Mathlib

open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_real_second_moment_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ n, Measurable (Y n))
    (hz : AEStronglyMeasurable Z P)
    (hInt : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P)
    (hB : ∀ n, (∫ ω, (Y n ω) ^ 2 ∂P) ≤ C)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable (fun ω => (Z ω) ^ 2) P ∧
      (∫ ω, (Z ω) ^ 2 ∂P) ≤ C := by sorry
