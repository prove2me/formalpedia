-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
-- name    : AvramDividend.Classical.avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:33:43.426434+00:00
-- url     : https://prove2.me/theorems/683662eb-234c-4ace-b15e-76c78870fea1
-- title:
--   Turn a vanishing positive source-error budget into an exact signed Fatou certificate
-- statement:
--   Suppose the original physical-grid payoff approximants F are measurable, L1, nonnegative and satisfy the source-faithful lower-Fatou clause, while a genuine combined compensated-jump/drift source M+B is L1, has nonpositive expectation, and bounds F with a deterministic nonnegative error e_n tending to zero. When the benchmark w(x)>0, scale payoff and both source terms by w/(w+e_n). The scaled witness has all exact source certificate clauses. Thus the hardest remaining original-process task may allow vanishing L1/deterministic error rather than exact finite-grid source domination. It does not assume the original certificate and preserves combined-only L1.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ) (hw : 0 < w) (Y : Ω → ℝ)
    (F M B : ℕ → Ω → ℝ) (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n)
    (he0 : Filter.Tendsto e Filter.atTop (nhds (0 : ℝ)))
    (hMeas : ∀ n, Measurable (F n))
    (hInt : ∀ n, Integrable (F n) P)
    (hPos : ∀ n, 0 ≤ᵐ[P] F n)
    (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w + (M n ω + B n ω) + e n)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        Filter.liminf (fun n => ENNReal.ofReal (F n ω)) Filter.atTop) :
    ∃ F' M' B' : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n) ∧ Integrable (F' n) P ∧
        0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M' n ω + B' n ω) P ∧
        (∫ ω, M' n ω + B' n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F' n ω ≤
        w + (M' n ω + B' n ω)) ∧
      (∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
        Filter.liminf (fun n => ENNReal.ofReal (F' n ω)) Filter.atTop) := by sorry
