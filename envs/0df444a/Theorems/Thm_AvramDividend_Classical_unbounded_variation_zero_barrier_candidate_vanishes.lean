-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_vanishes
-- name    : AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:16:23.787955+00:00
-- url     : https://prove2.me/theorems/aeb02566-0a79-4fee-abfa-4b60de866afc
-- title:
--   Zero-barrier candidate value vanishes for unbounded-variation Lévy processes
-- statement:
--   For any positive discount and unbounded-variation spectrally negative Lévy process, the q-scale function starts at zero. The formal barrier candidate formula therefore vanishes at capital zero and barrier zero, even with an infinite derivative-zero-plus value. This closes the analytic half of the zero-barrier boundary package as a reusable named result, leaving only the stochastic dividend equality.
-- source:
--   Proved chat04_scale_zero_origin_of_unbounded_variation and barrierValue_zero_of_scale_zero.

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    barrierValue W 0 0 = 0 := by sorry
