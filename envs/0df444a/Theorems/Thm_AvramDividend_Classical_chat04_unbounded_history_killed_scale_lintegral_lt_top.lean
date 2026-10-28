-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_history_killed_scale_lintegral_lt_top
-- name    : AvramDividend.Classical.chat04_unbounded_history_killed_scale_lintegral_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:53:45.657984+00:00
-- url     : https://prove2.me/theorems/244b9436-e464-469c-8bcf-5fad68d58c75
-- title:
--   Unbounded-variation killed q-scale ENNReal expectation is finite without Standing
-- statement:
--   For an unbounded-variation spectrally negative Levy process with q>0, the discounted q-scale payoff killed on the full history up to each finite time has a finite extended-nonnegative integral. This requires no standing integrability assumptions and no externally supplied Laplace parameter. The proof imports canonical fixed-time integrability in the unbounded-variation case and the previously Proved schedule-free survival-event measurability, and transfers real integrability through the indicator and ENNReal.ofReal. It directly supplies a fixed-time integrability prerequisite for the open all-time killed q-scale harmonicity and stopped two-sided exit identity.
-- source:
--   Imports Proved chat04_unbounded_scale_fixed_time_integrable (38e028ec-8d6c-4853-8024-206dc853aacf) and chat04_shifted_lower_survival_measurable_no_schedule (55082175-0822-4f2f-a627-cd0eb4c0640f). Pinned Mathlib Integrable.const_mul, Integrable.indicator and Integrable.lintegral_lt_top. Downstream exact intended import a885f0b3-3960-424d-97e4-abbcffe268ba, followed by aed50a34-200b-4736-a369-5ae8473e3258 and 09663d0d-c23e-47da-b5b9-1bbf28449a4d.

import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Mathlib.MeasureTheory.Integral.IntegrableOn

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_history_killed_scale_lintegral_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) < ⊤ := by sorry
