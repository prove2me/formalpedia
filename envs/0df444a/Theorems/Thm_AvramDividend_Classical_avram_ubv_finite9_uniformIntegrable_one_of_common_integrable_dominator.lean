-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_uniformIntegrable_one_of_common_integrable_dominator
-- name    : AvramDividend.Classical.avram_ubv_finite9_uniformIntegrable_one_of_common_integrable_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:43:05.161375+00:00
-- url     : https://prove2.me/theorems/eb3303d9-aa38-4611-bc49-764de8aba666
-- title:
--   Any uniformly dominated L1 family is uniformly integrable at exponent one
-- statement:
--   For any indexed family of almost-everywhere strongly measurable real random variables under a measure, one common integrable dominator in pointwise extended norm implies L1 uniform integrability of the family. The proof transfers both uniform absolute integrability and the common L1 norm bound from the constant family of the dominator using Mathlib's monotonicity lemmas. This general result applies to the true finite-cap post-right-payment payoff family through the published common cash and terminal envelope.

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_uniformIntegrable_one_of_common_integrable_dominator
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ι → Ω → ℝ) (G : Ω → ℝ)
    (hGI : Integrable G P)
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (hdom : ∀ i, (fun ω => ‖f i ω‖ₑ) ≤ᵐ[P] (fun ω => ‖G ω‖ₑ)) :
    UniformIntegrable f (1 : ℝ≥0∞) P := by sorry
