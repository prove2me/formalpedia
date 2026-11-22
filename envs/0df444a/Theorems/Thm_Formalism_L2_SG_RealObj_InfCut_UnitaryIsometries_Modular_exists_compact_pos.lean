-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_exists_compact_pos
-- name    : Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.exists_compact_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:16.025884+00:00
-- url     : https://prove2.me/theorems/5f207005-377d-49ce-9f97-9df798e7a60b
-- title:
--   Modular: exists compact pos
-- statement:
--   The Modular construction uses the exists compact pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EqOneOfZpowMem.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EqOneOfZpowMem.lean#L24-L28

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

theorem Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.exists_compact_pos : ∃ C : Set G, IsCompact C ∧ 0 < (Measure.haar : Measure G) C ∧
    (Measure.haar : Measure G) C ≠ ⊤ := by sorry
