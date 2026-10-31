-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
-- name    : AvramDividend.Classical.avram_wave3_04_strongAdapted_leftContinuous_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:52:20.243776+00:00
-- url     : https://prove2.me/theorems/5ae104c4-13de-429a-a344-76d22511259b
-- title:
--   Strongly adapted left-continuous processes are predictable on densely ordered separable time domains
-- statement:
--   A strongly adapted process whose sample paths are continuous from the left at every time, with left continuity understood as continuity within the closed past interval (−∞,t], is measurable for the predictable σ-algebra on a densely ordered, separable linearly ordered time domain with bottom. The proof constructs predictable simple-function approximations on finite rounded-down time grids and passes to the pointwise limit. This theorem supplies a verified predictable-process prerequisite for the original post-payment reserve in the Avram UBV verification programme; the controlled semimartingale Ito–Meyer estimate remains open.
-- source:
--   Adapted port of Remy Degenne's open-source Mathlib PR #44961, Apache-2.0: https://github.com/leanprover-community/mathlib4/pull/44961; pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 lacks its newer generator helper lemmas and IsLeftContinuous notation; the solution supplies both missing measurable-product facts and an equivalent continuity formulation.

import Mathlib

open MeasureTheory Filter Order TopologicalSpace
open scoped MeasureTheory NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave3_04_strongAdapted_leftContinuous_predictable
    {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [SeparableSpace ι]
    {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
    {𝓕 : Filtration ι m} {X : ι → Ω → β}
    (h_adap : StronglyAdapted 𝓕 X)
    (h_cont : ∀ ω t, ContinuousWithinAt (X · ω) (Set.Iic t) t) :
    IsStronglyPredictable 𝓕 X := by sorry
