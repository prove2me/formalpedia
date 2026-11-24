-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_comp_aut
-- name    : Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.comp_aut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:41.29708+00:00
-- url     : https://prove2.me/theorems/7b7dfe4d-fc4e-4a2d-9b4d-173ff446f3d2
-- title:
--   Modular: comp aut
-- statement:
--   The Modular construction uses the comp aut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EqOneOfZpowMem.lean#L95-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EqOneOfZpowMem.lean#L95-L115

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EqOneOfZpowMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
local notation "Δ" => Measure.modularCharacterFun (G := G)

theorem Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.comp_aut (α : G ≃ₜ* G) (g : G) : Δ (α g) = Δ g := by sorry
