-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a540_ae_bounded_real_integrable
-- name    : AvramDividend.Classical.avram_ga_a540_ae_bounded_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:38:35.134103+00:00
-- url     : https://prove2.me/theorems/8ef188f8-ec12-411a-9406-ad2779201529
-- title:
--   Almost-everywhere bounded real function has integrability from integrable constant
-- statement:
--   A strongly measurable real random variable with an almost-everywhere absolute upper bound by a constant is integrable whenever the dominating constant is integrable.
-- source:
--   Mathlib Integrable.mono for norm domination; generic bounded integrability for source Gaussian Taylor/generator cells

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a540_ae_bounded_real_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (f : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : AEStronglyMeasurable f P)
    (hb : ∀ᵐ ω ∂P, |f ω| ≤ K)
    (hconst : Integrable (fun _ : Ω => K) P) :
    Integrable f P := by sorry
