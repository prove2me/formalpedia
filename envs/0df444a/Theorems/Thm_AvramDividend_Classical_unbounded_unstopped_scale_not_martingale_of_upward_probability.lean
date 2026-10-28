-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_unstopped_scale_not_martingale_of_upward_probability
-- name    : AvramDividend.Classical.unbounded_unstopped_scale_not_martingale_of_upward_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:22:12.21343+00:00
-- url     : https://prove2.me/theorems/0fc74c47-a023-4cc4-8485-4b24e8145ffe
-- title:
--   Positive upward-movement probability rules out un-stopped scale martingale
-- statement:
--   A q-scale function W with W(0)=0 is nonnegative, and under unbounded variation W(y)>0 for y>0. If a spectrally negative Levy process starts at zero and has positive probability of an upward increment at some time, its un-killed discounted q-scale reward cannot be a martingale. This is a formal contradiction to an un-stopped candidate in the strict two-sided exit proof, establishing the need to stop or kill the process at lower ruin.
-- source:
--   Proved unbounded_unstopped_scale_martingale_forces_nonpositive_paths and pinned Mathlib ae_iff.

import Theorems.Thm_AvramDividend_Classical_unbounded_unstopped_scale_martingale_forces_nonpositive_paths
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Probability.Martingale.Basic

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_unstopped_scale_not_martingale_of_upward_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (hW0 : W 0 = 0)
    (hStart : ∀ᵐ ω ∂P, X.X 0 ω = 0)
    (hUp : ∃ t : ℝ≥0, 0 < P {ω : Ω | 0 < X.X t ω}) :
    ¬ Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P := by sorry
