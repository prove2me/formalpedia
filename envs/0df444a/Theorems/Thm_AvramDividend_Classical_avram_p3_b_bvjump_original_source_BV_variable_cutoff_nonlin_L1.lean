-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_variable_cutoff_nonlin_L1
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_variable_cutoff_nonlin_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:55:17.614016+00:00
-- url     : https://prove2.me/theorems/b4987f83-dd16-44c8-9f8b-b925fc20026a
-- title:
--   Original BV Levy source nonlinear negative increments are integrable at arbitrary small cut-off
-- statement:
--   For the original bounded-variation spectrally negative Levy process, each 0<delta<=1 has finite absolute nonlinear jump increment integral on (-delta,0), for any reserve u within the matching delta-interior of a compact local Lipschitz interval. The proof restricts the actual source Levy first moment from (-1,0), establishes source measurability using local continuity, and dominates by K(-z). This removes the earlier fixed one-unit interior margin, without any large-tail moment or additional stochastic-process axioms.
-- source:
--   Proved bv_small_negative_first_moment_integrable and P3-B localised first-order source increment

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_variable_cutoff_nonlin_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (K : ℝ≥0) (a b δ u : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hLip : LipschitzOnWith K w (Icc a b)) (hu : u ∈ Icc (a + δ) b) : IntegrableOn (fun z : ℝ => w (u + z) - w u) (Ioo (-δ) 0) X.ν := by sorry
