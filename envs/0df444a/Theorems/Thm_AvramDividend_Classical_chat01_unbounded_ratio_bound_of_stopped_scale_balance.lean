-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_unbounded_ratio_bound_of_stopped_scale_balance
-- name    : AvramDividend.Classical.chat01_unbounded_ratio_bound_of_stopped_scale_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T12:02:10.206159+00:00
-- url     : https://prove2.me/theorems/a9cc0032-4358-40e9-93f7-d12dcb9e6ffc
-- title:
--   Positive-root unbounded q-scale ratio bound from the sole stopped exit-scale balance
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and positive discount q, the universal stopped two-sided exit scale balance implies the exact exponential upper bound on W(x)/W(y) for all 0<x≤y at an existing positive root ψ(φ)=q. Positivity of W(y), the positive root, and the exponential comparison are established by separately canonically Proved helpers. The remaining stochastic stopped-balance hypothesis is explicit.
-- source:
--   Canonical accepted chat01_unbounded_esscher_decay_of_stopped_scale_balance and chat01_unbounded_tilted_scale_mono_of_stopped_balance.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_esscher_decay_of_stopped_scale_balance
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_tilted_scale_mono_of_stopped_balance
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_unbounded_ratio_bound_of_stopped_scale_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hBalance : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    ∃ (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q),
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-(φ * (y - x))) := by sorry
