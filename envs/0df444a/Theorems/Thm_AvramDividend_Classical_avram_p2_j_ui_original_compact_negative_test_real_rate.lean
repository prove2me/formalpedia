-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_negative_test_real_rate
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_compact_negative_test_real_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:01:23.263367+00:00
-- url     : https://prove2.me/theorems/c404a969-2a32-4c0b-9fcd-0d09120b3dce
-- title:
--   Source-exact original Lévy negative compact test rate without auxiliary support cutoffs
-- statement:
--   For every continuous real compactly supported test whose topological support is strictly negative, prove the genuine original Levy marginal right-derivative integral rate against its actual negative Levy measure. Derive the compact support band cutoffs and apply the already-Proved P2-I source theorem; finally rewrite the positive-filter reciprocal branch to a Bochner integral quotient. No new Levy process or jump compensator is assumed.

import Mathlib.Topology.Algebra.Order.Field
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_support_has_band
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_compact_test_real_rate

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_j_ui_original_compact_negative_test_real_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    Tendsto (fun h : ℝ =>
      (∫ ω, g (X.X (Real.toNNReal h) ω) ∂P) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y : ℝ, g y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by sorry
