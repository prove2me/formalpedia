-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb74_finite_measure_component_envelopes_compensated_positive_residual
-- name    : AvramDividend.Classical.avram_bvb74_finite_measure_component_envelopes_compensated_positive_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:06:03.802768+00:00
-- url     : https://prove2.me/theorems/626ff1c5-aa75-4abd-9498-cd209cb5d872
-- title:
--   Finite-measure compensated cash positive residual has integrable componentwise envelope
-- statement:
--   Corrected finite-measure source of original BVB70: under finite measure P, individually integrable original cash, marked jump and compensator rows dominated by respective common integrable envelopes, the positive compensated residual has a common integrable envelope and measurable rows. Finite measure is essential because the offset |b| is constant. The full original Lévy measure P is a probability.
-- source:
--   BVB70 CE 36529 established missing finite measure; triangle inequality and Bochner integrability under finite P

import Mathlib
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb74_finite_measure_component_envelopes_compensated_positive_residual
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
