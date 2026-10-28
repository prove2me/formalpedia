-- Prove2me | Theorems.Thm_AvramDividend_Classical_isStoppingTime_iSup_countable
-- name    : AvramDividend.Classical.isStoppingTime_iSup_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:45:41.342225+00:00
-- url     : https://prove2.me/theorems/d80090e7-8907-4a02-bd2d-ebf5808f5650
-- title:
--   Countable pointwise supremum of stopping times is a stopping time without filtration right-continuity
-- statement:
--   For a filtration over nonnegative real time and a countable family of WithTop-valued stopping times, their pointwise supremum is again a stopping time, without assuming right-continuity of the filtration. The key identity is {sup_k τ_k≤t}=⋂_k{τ_k≤t}; the right side is a countable intersection of filtration-t-measurable events. This supports taking increasing limits of approximating first-passage times, a necessary step in reconstructing the true continuous-time first hit from dense-grid observations of slightly lower levels.
-- source:
--   Pinned Mathlib Order.CompleteLattice.Basic iSup_le_iff, and Probability.Process.Stopping IsStoppingTime definition.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.isStoppingTime_iSup_countable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    {κ : Type*} [Countable κ]
    (τ : κ → Ω → WithTop ℝ≥0)
    (hτ : ∀ k : κ, IsStoppingTime 𝓕 (τ k)) :
    IsStoppingTime 𝓕 (fun ω : Ω => ⨆ k : κ, τ k ω) := by sorry
