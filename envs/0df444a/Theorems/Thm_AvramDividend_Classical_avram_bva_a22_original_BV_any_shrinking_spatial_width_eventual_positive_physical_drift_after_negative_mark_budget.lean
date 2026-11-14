-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:57:58.055198+00:00
-- url     : https://prove2.me/theorems/9f2b0aa3-8fcb-450c-839f-b5573f650ac3
-- title:
--   Original BV positive physical drift eventually dominates discount times any shrinking spatial boundary plus true negative-mark truncated moment, without rate restriction
-- statement:
--   In the genuine original bounded-variation spectrally negative Levy process X with strictly positive physical drift, take any prescribed positive spatial widths epsilon(n) no larger than one and tending to zero, without imposing any relation to the strict physical uniform grid. For any real discount coefficient q, beyond a deterministic row index the true original small-boundary budget q epsilon(n) + integral over actual negative Levy marks of min(epsilon(n),−z) is strictly below X.drift. The already Proved original arbitrary-rate BV first moment vanishes, while q epsilon(n) vanishes, so their sum eventually falls below positive drift. This upgrades the older existential width choice to a uniform eventual statement along every prescribed shrinking width, supporting the original BVA96 any-cofinal-band near-zero jump/physical drift treatment without finite jump activity or global generator L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hd : 0 < X.drift) (q : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      q * ε n + (∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν) <
        X.drift := by sorry
