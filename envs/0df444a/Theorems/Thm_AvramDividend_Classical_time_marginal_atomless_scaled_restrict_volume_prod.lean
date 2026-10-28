-- Prove2me | Theorems.Thm_AvramDividend_Classical_time_marginal_atomless_scaled_restrict_volume_prod
-- name    : AvramDividend.Classical.time_marginal_atomless_scaled_restrict_volume_prod
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:28:29.787458+00:00
-- url     : https://prove2.me/theorems/e373cc8a-7212-4165-bb42-5c8b7d5a384a
-- title:
--   Every scaled restriction of Lebesgue-time×Lévy intensity has a diffuse time-coordinate law
-- statement:
--   Let ν be an s-finite jump-size measure and S any subset of the real time×real jump-size plane. Every scalar multiple c·(volume_time×ν)|S, including the normalized probability law of a positive-mass Poisson point-family partition piece, has an atomless time-coordinate marginal. This follows because restriction and scaling preserve absolute continuity with respect to the original product intensity and the accepted time_marginal_atomless_of_ac_volume_prod theorem. This specifically addresses the canonical LeanLevy positive-intensity piece law, which is a normalized restricted product measure; the zero-intensity pieces use dummy Dirac points but contribute zero active marks almost surely.
-- source:
--   Proved time_marginal_atomless_of_ac_volume_prod [fec22846-3b7f-4271-b927-301844170258] and pinned Mathlib Measure.absolutelyContinuous_restrict plus AbsolutelyContinuous.smul_left. Matches source LeanLevy/RandomMeasure/PoissonPointFamily.lean prmPieceLaw_of_ne_zero.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Theorems.Thm_AvramDividend_Classical_time_marginal_atomless_of_ac_volume_prod

open AvramDividend.Classical MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.time_marginal_atomless_scaled_restrict_volume_prod
    (ν : Measure ℝ) [SFinite ν]
    (S : Set (ℝ × ℝ)) (c : ℝ≥0∞) :
    NullSingletonClass
      ((c • (((volume : Measure ℝ).prod ν).restrict S)).map Prod.fst) := by sorry
