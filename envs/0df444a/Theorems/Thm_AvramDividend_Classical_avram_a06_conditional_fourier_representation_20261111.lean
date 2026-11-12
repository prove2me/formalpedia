-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_conditional_fourier_representation_20261111
-- name    : AvramDividend.Classical.avram_a06_conditional_fourier_representation_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:56:32.108562+00:00
-- url     : https://prove2.me/theorems/5d7ad8be-b29a-496c-ad14-ad85bf4ad3ad
-- title:
--   Conditional Fourier formula for IID marks over random count-grid blocks
-- statement:
--   For an ordered random count grid independent of an IID mark stream and assuming the already proved fixed-grid Fourier factorisation, construct for each frequency measurable complex functions of each count increment such that the joint and marginal random-block characteristic functions are represented as expectations of their product and of their individual terms. This is a genuinely conditional-law step; it does not assume independent count increments. Combining this theorem with Mathlib's iIndepFun.integral_fun_prod_comp will prove the random-count Fourier mixing theorem efc6c2ea.

import Mathlib
open MeasureTheory Set ProbabilityTheory Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_conditional_fourier_representation_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
            (t.ofLp i)) :
    ∀ t : WithLp 2 (Fin n → ℝ), ∃ φ : Fin n → ℕ → ℂ,
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
          ∫ ω, ∏ i : Fin n, φ i (N i.succ ω - N i.castSucc ω) ∂P
      ∧ ∀ i : Fin n, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
          (t.ofLp i) =
          ∫ ω, φ i (N i.succ ω - N i.castSucc ω) ∂P := by sorry
