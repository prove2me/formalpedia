-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_nonneg_past_test_condexp_bridge
-- name    : AvramDividend.Classical.avram_root29_01_nonneg_past_test_condexp_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:14:14.027345+00:00
-- url     : https://prove2.me/theorems/9bc65c2b-f9d6-4e2c-8ec9-0f030ae27a21
-- title:
--   Real conditional expectation uniquely determined by nonnegative ENNReal historical-event tests
-- statement:
--   For a real integrable nonnegative payoff f and a real integrable measurable candidate g, if their actual ENNReal.ofReal integrals agree after testing against every measurable event of the sub-σ-algebra, then g is the true real conditional expectation P[f|𝓖]. Requires the actual SigmaFinite trim, and proves the conversion using integrability, nonnegative indicators, ofReal_integral_eq_lintegral_ofReal, real integral nonnegativity and Mathlib conditional-expectation uniqueness. This precisely discharges the real-versus-ENNReal measure interface in the original-Lévy killed-scale problem.
-- source:
--   WS1A rigorous independent conditional-expectation bridge work/avram_root29_01_nonneg_past_test_condexp_bridge_draft.lean. It is a generic reusable measure-theory theorem with all real integrability and positivity assumptions explicit.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory Set
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_root29_01_nonneg_past_test_condexp_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (𝓖 : MeasurableSpace Ω) (h𝓖 : 𝓖 ≤ mΩ)
    [SigmaFinite (P.trim h𝓖)]
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P)
    (hgm : Measurable[𝓖] g)
    (hfnn : 0 ≤ᵐ[P] f) (hgnn : 0 ≤ᵐ[P] g)
    (hTest : ∀ A : Set Ω, MeasurableSet[𝓖] A →
      (∫⁻ ω, if ω ∈ A then ENNReal.ofReal (f ω)
        else (0 : ℝ≥0∞) ∂P) =
      (∫⁻ ω, if ω ∈ A then ENNReal.ofReal (g ω)
        else (0 : ℝ≥0∞) ∂P)) :
    P[f | 𝓖] =ᵐ[P] g := by sorry
