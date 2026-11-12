-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb98_finite_step_stronglyMeasurable
-- name    : AvramDividend.Classical.avram_gb98_finite_step_stronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:18:10.448726+00:00
-- url     : https://prove2.me/theorems/781cd66f-aa2f-4d72-bda8-29c3bae2fd1b
-- title:
--   Finite deterministic step sum of strongly measurable random coefficients is strongly measurable
-- statement:
--   At a fixed time, each deterministic interval indicator is constant in the random outcome, so each selected coefficient is strongly measurable and their finite sum remains strongly measurable.
-- source:
--   Necessary and reusable sublemma of original Gaussian pointwise gb96.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gb98_finite_step_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (s : Finset ℕ) (a b : ℕ → ℝ) (g : ℕ → Ω → ℝ)
    (hg : ∀ i ∈ s, StronglyMeasurable (g i)) (t : ℝ) :
    StronglyMeasurable (fun ω =>
      s.sum (fun i => if a i ≤ t ∧ t < b i then g i ω else 0)) := by sorry
