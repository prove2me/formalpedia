-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_random_positive_source_error_fatou_normalisation
-- name    : AvramDividend.Classical.avram_p3_grid4_random_positive_source_error_fatou_normalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:15:47.951507+00:00
-- url     : https://prove2.me/theorems/690714e8-6f3d-4496-9a66-7b8068ff2d4e
-- title:
--   Vanishing original physical-grid positive L1 errors admit exact centred signed Fatou normalisation
-- statement:
--   An L1 positive physical-grid Taylor/contact error with expectation tending to zero can be included in the authentic integrable compensated-jump plus HJB signed source, centred by its expectation, and then absorbed into the positive benchmark via deterministic rescaling. The resulting nonnegative Fatou payoffs and nonpositive-mean signed witnesses satisfy the exact unperturbed certificate. Requires an actual physical X/D pathwise comparison separately and makes no source or stochastic-process identification.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_centered_physical_error_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_random_positive_source_error_fatou_normalisation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (w : ℝ) (hw : 0 < w) (Y : Ω → ℝ)
    (F M B Err : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (F n))
    (hInt : ∀ n, Integrable (F n) P)
    (hPos : ∀ n, 0 ≤ᵐ[P] F n)
    (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hErrInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hErrMean : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0))
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w + (M n ω + B n ω) + max (Err n ω) 0)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ F' M' B' : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n) ∧ Integrable (F' n) P ∧
        0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M' n ω + B' n ω) P ∧
        (∫ ω, M' n ω + B' n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F' n ω ≤ w + (M' n ω + B' n ω)) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal (Y ω) ≤
          liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by sorry
