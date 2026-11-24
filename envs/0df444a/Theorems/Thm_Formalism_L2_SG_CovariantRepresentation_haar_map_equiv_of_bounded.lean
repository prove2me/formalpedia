-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_haar_map_equiv_of_bounded
-- name    : Formalism.L2.SG.CovariantRepresentation.haar_map_equiv_of_bounded
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:08.555646+00:00
-- url     : https://prove2.me/theorems/3b03d894-540f-41fb-8bb1-435f268450b0
-- title:
--   Covariant Representation: haar map equiv of bounded
-- statement:
--   The Covariant Representation construction uses the haar map equiv of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L244-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L244-L274

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

theorem Formalism.L2.SG.CovariantRepresentation.haar_map_equiv_of_bounded (μ : Measure H) [IsHaarMeasure μ] (α : H ≃ₜ* H) {V L : Set H}
    (hV : IsCompact V) (hV1 : V ∈ 𝓝 (1 : H)) (hL : IsCompact L)
    (hb : ∀ n : ℕ, (⇑α)^[n] '' V ⊆ L ∧ (⇑α.symm)^[n] '' V ⊆ L) : μ.map α = μ := by sorry
