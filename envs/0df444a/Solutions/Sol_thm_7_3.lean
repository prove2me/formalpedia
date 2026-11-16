-- Prove2me | solution 1 for thm_7_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:46.306311+00:00
-- url     : https://prove2.me/submissions/b6d9d444-4590-47fc-a797-e92fbbf373b6

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory


/--  ## Theorem 7.4 Fatou lemma
Exported statement for Fatou's lemma in the textbook
nonnegative setting, modeled as an `ENNReal`-valued sequence.

We apply an equivalent API in Mathlib.
-/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (X : ℕ → Ω → ENNReal)
  (hX : ∀ n, Measurable (X n)) :
    ∫⁻ ω, Filter.liminf (fun n => X n ω) Filter.atTop ∂μ ≤
      Filter.liminf (fun n => ∫⁻ ω, X n ω ∂μ) Filter.atTop := by
  exact lintegral_liminf_le hX

