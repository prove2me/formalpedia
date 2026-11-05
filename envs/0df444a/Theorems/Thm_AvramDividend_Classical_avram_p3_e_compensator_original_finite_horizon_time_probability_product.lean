-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_finite_horizon_time_probability_product
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_finite_horizon_time_probability_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:12:00.348667+00:00
-- url     : https://prove2.me/theorems/c8d79934-f595-4437-82d8-27bfef2c3ced
-- title:
--   Original stopped BV bounded-horizon time-probability product measure has finite mass
-- statement:
--   For the actual original SpectrallyNegativeLevy process, the stopped verification's time measure is the pushforward under Real.toNNReal of Lebesgue measure restricted to [0,T]. Its product with the original probability measure P has finite total mass automatically. This removes the separate time-product finiteness premise used by the original predictable compensator and permits straightforward dominated drift integrability.
-- source:
--   Original X.isProbability together with Mathlib's Real.isFiniteMeasure_restrict_Icc, Measure.isFiniteMeasure_map, and product IsFiniteMeasure instance. No replacement measure or stochastic-process assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_finite_horizon_time_probability_product
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
(((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) Set.univ) < ⊤ := by sorry
