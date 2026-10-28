-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_stopped_scale_of_near_zero
-- name    : AvramDividend.Classical.chat04_unbounded_zero_start_stopped_scale_of_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:56:26.617774+00:00
-- url     : https://prove2.me/theorems/2c9771ff-7e01-4869-b2df-e0491b297d1a
-- title:
--   Unbounded-variation stopped q-scale identity at zero from negative-near-zero regularity
-- statement:
--   Under unbounded variation and almost-sure negative path increments arbitrarily close to time zero, the strict first downward exit is instantaneous. Consequently the discounted event of strict upward passage before downward exit has expectation zero and the stopped q-scale identity at zero reserve holds for every positive upper barrier. This is the fully factored x=0 boundary case of the root-connected stopped-scale theorem.
-- source:
--   Composes Proved chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero (8029c619-18d2-4bb2-af3b-90196ce32411) and pathwise chat04_down_exit_time_zero_of_negative_near_zero (ac9a5651-010e-4c40-b205-951565722f97, proof fbd9fd52 pending). A self-contained x=0 boundary for the Open aed50a34 two-sided stopped scale identity, parent 3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_zero_of_negative_near_zero
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_zero_start_stopped_scale_of_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hnear : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < 0), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W 0) := by sorry
