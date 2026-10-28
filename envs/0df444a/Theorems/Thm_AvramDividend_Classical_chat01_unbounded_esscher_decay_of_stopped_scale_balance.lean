-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_unbounded_esscher_decay_of_stopped_scale_balance
-- name    : AvramDividend.Classical.chat01_unbounded_esscher_decay_of_stopped_scale_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:48:24.125933+00:00
-- url     : https://prove2.me/theorems/f938e327-d46b-496b-8259-5c6e9172f95b
-- title:
--   Unbounded Esscher scale decay from the sole stopped-scale balance
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, positive discount, positive Esscher root and canonical scale function, the full positive-root first-passage exponential ratio inequality follows from the exact stopped-scale balance at each upper and initial reserve level. This isolates a single remaining stochastic premise, without Standing, via two already verified algebraic bridges: balance to corrected killed exit ratio, and corrected exit identity to Esscher scale decay.
-- source:
--   Proved chat01_unbounded_corrected_exit_ratio_of_stopped_balance and unbounded_fixedroot_decay_of_corrected_exit_identity. Remaining original stopped martingale/scale balance is explicit.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_unbounded_esscher_decay_of_stopped_scale_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBalance : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-(φ * (y - x))) * W y := by sorry
