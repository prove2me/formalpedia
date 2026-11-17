-- Prove2me | solution 1 for heine_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:14.253321+00:00
-- url     : https://prove2.me/submissions/7fea71ce-5937-4b29-bfae-0d39a70b9b85

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_4_F000
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Bounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Metric Bornology

theorem solution (A : Set ℝ) :
    IsCompactTextbook A ↔
    (∀ {ι : Type} (U : ι → Set ℝ), (∀ i, IsOpen (U i)) → (A ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i) := by
  -- 1. Unfold our textbook definition of compactness
  rw [IsCompactTextbook]
  -- 2. Use the Heine-Borel theorem for proper spaces (like ℝ)
  -- to relate Closed + Bounded to Mathlib's IsCompact
  rw [← Metric.isCompact_iff_isClosed_bounded]
  -- 3. Use the topological definition of IsCompact to relate it to
  -- the finite subcover property
  exact isCompact_iff_finite_subcover
