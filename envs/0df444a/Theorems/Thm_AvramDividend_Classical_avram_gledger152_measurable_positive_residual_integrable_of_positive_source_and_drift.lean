-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger152_measurable_positive_residual_integrable_of_positive_source_and_drift
-- name    : AvramDividend.Classical.avram_gledger152_measurable_positive_residual_integrable_of_positive_source_and_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:15:30.326612+00:00
-- url     : https://prove2.me/theorems/75808414-43a1-4b81-8b66-05efb514a5fb
-- title:
--   Positive source residual remains integrable after measurable L1 drift subtraction
-- statement:
--   For the original Gaussian stopped source use f = S_m-M_m and g = G_m. If the positive original source difference is integrable, the signed original source is measurable, and the discounted generator-grid drift is integrable, then the positive corrected residual max(S-M-G,0) is integrable. This preserves a necessary independent measurable-source hypothesis, avoiding the invalid inference that integrability of an absolute value implies measurability.
-- source:
--   Pointwise max(f-g,0)≤max(f,0)+|g|, strong measurability and integrable domination. Used to close source-exact gledger144 together with Proved gledger52.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gledger152_measurable_positive_residual_integrable_of_positive_source_and_drift
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ)
    (hfplus : Integrable (fun ω => max (f ω) (0 : ℝ)) P)
    (hfmeas : AEStronglyMeasurable f P)
    (hg : Integrable g P) :
    Integrable (fun ω => max (f ω - g ω) (0 : ℝ)) P := by sorry
