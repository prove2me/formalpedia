-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_modular_eq_one_of_mem
-- name    : Formalism.L2.SG.CovariantRepresentation.modular_eq_one_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:00.675306+00:00
-- url     : https://prove2.me/theorems/6f5f61b9-df6b-427d-8e4a-26d463166ca1
-- title:
--   Covariant Representation: modular eq one of mem
-- statement:
--   The Covariant Representation construction uses the modular eq one of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L98-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L98-L126

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

theorem Formalism.L2.SG.CovariantRepresentation.modular_eq_one_of_mem (μ : Measure H) [IsHaarMeasure μ] (Γ : Subgroup H) [Countable Γ]
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K)
    {δ : H} (hδ : δ ∈ Γ) : modularCharacterFun δ = 1 := by sorry
