-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_map_mul_right_eq_modular
-- name    : Formalism.L2.SG.CovariantRepresentation.map_mul_right_eq_modular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:30.616897+00:00
-- url     : https://prove2.me/theorems/74f56cc6-ad11-48a0-9c49-e87420e14314
-- title:
--   Covariant Representation: map mul right eq modular
-- statement:
--   The Covariant Representation construction uses the map mul right eq modular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L93-L96

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

theorem Formalism.L2.SG.CovariantRepresentation.map_mul_right_eq_modular (μ : Measure H) [IsHaarMeasure μ] (g : H) :
    μ.map (· * g) = ((modularCharacterFun g : ℝ≥0) : ℝ≥0∞) • μ := by sorry
