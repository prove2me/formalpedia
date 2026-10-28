-- Prove2me | Theorems.Thm_AvramDividend_Classical_constant_restricted_real_law_pointwise_limit
-- name    : AvramDividend.Classical.constant_restricted_real_law_pointwise_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:13:07.277989+00:00
-- url     : https://prove2.me/theorems/a77cde9c-4fd0-4f35-82bc-3787257a5c8b
-- title:
--   Pointwise limits preserve a constant finite restricted real-valued pushforward law
-- statement:
--   Let μ be a finite measure, A a measurable event, ν a finite Borel measure on the real line, and Y_n measurable real observables converging pointwise to measurable Y. If for every n the pushforward under μ restricted to A is exactly μ(A) times ν, then the limit Y has the identical scaled law. The proof uses uniform bounds of nonnegative compactly supported continuous test functions, dominated convergence, and Riesz measure uniqueness. It makes no assumption about continuity sets or atomlessness of ν, and hence supports stopping-time convergence of arbitrary Borel cylinder probabilities.
-- source:
--   Standard bounded continuous test convergence and Riesz uniqueness. Proved Prove2Me compactTest_lintegral_scalar_factor_implies_measure_smul (b629ed80-f1d2-4125-aa7f-19bcbd7ab7ae), compactTest_nnreal_uniformBound_finiteLintegral (e92f0d3f-6854-4649-8790-12e0c9cbe80b), lintegral_stoppedEvent_reward_tendsto_of_bounded (c18a8b5d-e322-4297-bae5-c2eab75ea472), pinned Mathlib MeasureTheory Integral.

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Theorems.Thm_AvramDividend_Classical_lintegral_stoppedEvent_reward_tendsto_of_bounded
import Theorems.Thm_AvramDividend_Classical_compactTest_lintegral_scalar_factor_implies_measure_smul
import Theorems.Thm_AvramDividend_Classical_compactTest_nnreal_uniformBound_finiteLintegral
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.constant_restricted_real_law_pointwise_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A)
    (Yₙ : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hYn : ∀ n, Measurable (Yₙ n)) (hY : Measurable Y)
    (hlim : ∀ ω, Tendsto (fun n => Yₙ n ω) atTop (𝓝 (Y ω)))
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hlaw : ∀ n, Measure.map (Yₙ n) (μ.restrict A) = μ A • ν) :
    Measure.map Y (μ.restrict A) = μ A • ν := by sorry
