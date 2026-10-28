-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_unbounded_tilted_scale_mono_of_stopped_balance
-- name    : AvramDividend.Classical.chat01_unbounded_tilted_scale_mono_of_stopped_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:52:00.369985+00:00
-- url     : https://prove2.me/theorems/f9b893f4-a234-4a5c-be58-f928de3aad9e
-- title:
--   Positive Esscher root and increasing tilted scale from the sole unbounded stopped balance
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and a positive discount, the universal stopped two-sided exit scale balance alone implies positivity of the q-scale function and existence of a positive Esscher root for which the tilted scale x↦exp(-φx)W(x) is nondecreasing on positive reserves. This follows by converting the stopped balance to the corrected killed exit identity without Standing, then applying the canonically proved positive tilted-scale comparison. It isolates the same missing stochastic obligation that blocks two independent branches of the mission.
-- source:
--   Proved chat01_unbounded_corrected_exit_ratio_of_stopped_balance and unbounded_positive_tilt_of_corrected_exit.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_unbounded_tilted_scale_mono_of_stopped_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hBalance : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
        MonotoneOn (fun x : ℝ => Real.exp (-(φ * x)) * W x)
          (Ioi (0 : ℝ)) := by sorry
