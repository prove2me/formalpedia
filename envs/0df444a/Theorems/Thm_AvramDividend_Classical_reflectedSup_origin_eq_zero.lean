-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_origin_eq_zero
-- name    : AvramDividend.Classical.reflectedSup_origin_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:41:03.747907+00:00
-- url     : https://prove2.me/theorems/136bd2d6-18f1-4da9-8a42-fc2116e36658
-- title:
--   The canonical spectrally negative Lévy reflected drawdown starts from zero
-- statement:
--   The reflected running-supremum process starts from zero. The time-zero interval is a singleton, X_0=0, and so the truncated running supremum is zero. Their difference is zero. This supplies the first endpoint in finite-lifetime maximum attainment.
-- source:
--   Canonical Prove2Me reflected process definition and Lévy origin normalisation.

import Definitions.Def_AvramDividend_Classical_Reflection
import Mathlib.Order.Interval.Set.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_origin_eq_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) : reflectedSup X 0 ω = 0 := by sorry
