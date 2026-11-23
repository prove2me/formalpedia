-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_haar_preimage
-- name    : Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.haar_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:31.977804+00:00
-- url     : https://prove2.me/theorems/53095f3e-d42f-45fc-a2dc-f42d8f891edd
-- title:
--   Modular: haar preimage
-- statement:
--   The Modular construction uses the haar preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EqOneOfZpowMem.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EqOneOfZpowMem.lean#L18-L22

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

theorem Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.haar_preimage (g : G) {A : Set G} (hA : MeasurableSet A) :
    (Measure.haar : Measure G) ((· * g) ⁻¹' A) = (Δ g : ℝ≥0∞) * (Measure.haar : Measure G) A := by sorry
