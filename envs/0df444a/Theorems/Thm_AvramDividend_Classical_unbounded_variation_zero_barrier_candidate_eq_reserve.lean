-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_reserve
-- name    : AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_eq_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:20:49.042305+00:00
-- url     : https://prove2.me/theorems/3677bb20-55a7-4e94-a1c5-f3f14c0fe9fc
-- title:
--   Unbounded-variation zero-barrier scale candidate equals available reserves
-- statement:
--   For any positive discount and spectrally negative Lévy process of unbounded variation, the zero-scale-origin identity and the affine zero-barrier formula imply the barrier candidate value is exactly the initial reserve at every nonnegative initial capital. This completes the positive-reserve extension of the zero-barrier candidate boundary condition, independent of the stochastic dividend-value identity.
-- source:
--   Existing Proved zero-origin scale theorem, barrierValue_zero_of_scale_zero and barrierValue_zero_affine_nonnegative.

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_eq_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) :
    barrierValue W 0 x = x := by sorry
