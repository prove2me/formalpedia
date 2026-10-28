-- Prove2me | Theorems.Thm_AvramDividend_Classical_time_marginal_atomless_of_ac_volume_prod
-- name    : AvramDividend.Classical.time_marginal_atomless_of_ac_volume_prod
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:22:11.795664+00:00
-- url     : https://prove2.me/theorems/fec22846-3b7f-4271-b927-301844170258
-- title:
--   Any measure absolutely continuous with respect to time-Lebesgue times jump intensity has a diffuse time-coordinate marginal
-- statement:
--   Let ν be an s-finite Borel measure on jump sizes, and let η be any measure on real time×real jump-size space which is absolutely continuous with respect to Lebesgue-time × ν. The time-coordinate marginal of η is atomless: every singleton time has probability or measure zero. A fixed-time slice {t}×ℝ has product intensity zero since Lebesgue gives no mass to a singleton. Absolute continuity transfers this nullness to η; projecting to time identifies its singleton preimage with the slice. This is the key diffuse-time measure-theoretic prerequisite for canonical Poisson point-family arrival times under the normalised restriction of the product intensity to nonzero-mass partition pieces. For zero-mass pieces the canonical model may use a dummy Dirac point and they must instead be shown inactive almost surely.
-- source:
--   Pinned Mathlib MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.AbsolutelyContinuous, MeasureTheory.nullSingletonClass_volume (Mathlib.MeasureTheory.Measure.Lebesgue.Basic), Measure.map_apply. Canonical Lévy jump construction in LeanLevy/RandomMeasure/PoissonPointFamily.lean uses piece-normalised product intensities for point laws.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.time_marginal_atomless_of_ac_volume_prod
    (ν : Measure ℝ) [SFinite ν]
    (η : Measure (ℝ × ℝ))
    (hη : η ≪ ((volume : Measure ℝ).prod ν)) :
    NullSingletonClass (η.map Prod.fst) := by sorry
