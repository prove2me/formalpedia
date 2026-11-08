-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_countable_positive_grid_prejump
-- name    : AvramDividend.Classical.avram_bv_stieltjes10_original_countable_positive_grid_prejump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:25:26.122138+00:00
-- url     : https://prove2.me/theorems/e26f2e74-1984-463f-8981-26ab8145a3f3
-- title:
--   All positive deterministic grid left-limits equal original prepayment reserve almost surely
-- statement:
--   For a countable deterministic grid whose sample times are strictly positive, one common probability-one event identifies the left-limit of the original post-rightpayment sampled reserve with the true prepayment riskProcess at every grid time. This combines the proved fixed-time Lévy left-continuity a.e. and the exact prepost left-limit identity, leaving time zero separate.
-- source:
--   Positive-time P3-F2 fixed-horizon left-limit 50564343 and pathwise pre/post left-limit caa7f605, countable intersection via pinned ae_all_iff, separate initial atom as zero-prepost theorem.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_controlled_fixed_horizon_leftLim_eq_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_stieltjes10_original_countable_positive_grid_prejump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℝ≥0) (hu : ∀ n, 0 < u n) :
    ∀ᵐ ω ∂P, ∀ n,
      Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (u n) =
        riskProcess X x D (u n) ω := by sorry
