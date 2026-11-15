-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb70_finite_measure_integrable_envelope_majorises_positive_cash_residual
-- name    : AvramDividend.Classical.avram_bvb70_finite_measure_integrable_envelope_majorises_positive_cash_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:41:59.839679+00:00
-- url     : https://prove2.me/theorems/24298d12-760a-4694-90c7-0898ffb7f4ba
-- title:
--   Finite-mass corrected common L1 envelope for compensated positive cash residual
-- statement:
--   Corrected version of original bvb70: the constant base b requires a finite measure for its absolute value to be integrable. Under IsFiniteMeasure P, original rowwise F,J,V integrability and uniform integrable component envelopes furnish a common integrable dominator |b|+Fbound+Jbound+Vbound for the positive residual max(F_n-(b+J_n-V_n),0). The original statement without finite mass is false on infinite counting measure. This lemma is reusable for probability measure models.
-- source:
--   Correction of bvb70 missing finite measure hypothesis; authoring for Avram finite-activity BV source dominated convergence

import Mathlib
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb70_finite_measure_integrable_envelope_majorises_positive_cash_residual
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F J V : ℕ → Ω → ℝ) (b : ℝ)
    (Fbound Jbound Vbound : Ω → ℝ)
    (hFi : Integrable Fbound P) (hJi : Integrable Jbound P)
    (hVi : Integrable Vbound P)
    (hFRows : ∀ n, Integrable (F n) P)
    (hJRows : ∀ n, Integrable (J n) P)
    (hVRows : ∀ n, Integrable (V n) P)
    (hFdom : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ Fbound ω)
    (hJdom : ∀ n, ∀ᵐ ω ∂P, ‖J n ω‖ ≤ Jbound ω)
    (hVdom : ∀ n, ∀ᵐ ω ∂P, ‖V n ω‖ ≤ Vbound ω) :
    let E : ℕ → Ω → ℝ := fun n ω =>
      max (F n ω - (b + (J n ω - V n ω))) 0
    ∃ Henv : Ω → ℝ,
      Integrable Henv P ∧
      (∀ n, AEStronglyMeasurable (E n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, ‖E n ω‖ ≤ Henv ω) := by sorry
