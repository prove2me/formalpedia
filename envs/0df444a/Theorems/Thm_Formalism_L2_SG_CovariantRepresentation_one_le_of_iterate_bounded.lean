-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_one_le_of_iterate_bounded
-- name    : Formalism.L2.SG.CovariantRepresentation.one_le_of_iterate_bounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:08.231806+00:00
-- url     : https://prove2.me/theorems/8de2f17e-6057-4a5d-bb38-0921c9616831
-- title:
--   Covariant Representation: one le of iterate bounded
-- statement:
--   The Covariant Representation construction uses the one le of iterate bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L215-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L215-L242

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.CovariantRepresentation
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem Formalism.L2.SG.CovariantRepresentation.one_le_of_iterate_bounded (μ : Measure H) [IsHaarMeasure μ] {f : H → H} (hf : Continuous f)
    (hinj : Function.Injective f) {c : ℝ≥0∞} (hc : μ.map f = c • μ) {V L : Set H} (hV : IsCompact V)
    (hV1 : V ∈ 𝓝 (1 : H)) (hL : IsCompact L) (hb : ∀ n : ℕ, f^[n] '' V ⊆ L) : 1 ≤ c := by sorry
