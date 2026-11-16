-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a551_quadratic_domination_integrable
-- name    : AvramDividend.Classical.avram_ga_a551_quadratic_domination_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:54:52.643086+00:00
-- url     : https://prove2.me/theorems/fd04e588-617d-4760-bde6-d86a886d2f13
-- title:
--   A quadratically dominated measurable random variable is integrable
-- statement:
--   A real random variable is integrable if it is almost everywhere strongly measurable and its absolute value is dominated by K times one plus a square-integrable raw increment, with integrable constant K.
-- source:
--   Integrable.mono using integrability of K + K*z^2 and nonnegativity from squared term

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a551_quadratic_domination_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (f z : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : AEStronglyMeasurable f P)
    (hz2 : Integrable (fun ω => (z ω)^2) P)
    (hconst : Integrable (fun _ : Ω => K) P)
    (hbound : ∀ᵐ ω ∂P, |f ω| ≤ K * (1 + (z ω)^2)) :
    Integrable f P := by sorry
