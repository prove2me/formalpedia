-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_eq_one_of_zpow_mem
-- name    : Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.eq_one_of_zpow_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:40.541655+00:00
-- url     : https://prove2.me/theorems/837b638c-9a6d-4514-8ba0-4d44591b4822
-- title:
--   Modular: eq one of zpow mem
-- statement:
--   The Modular construction uses the eq one of zpow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EqOneOfZpowMem.lean#L30-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EqOneOfZpowMem.lean#L30-L68

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

theorem Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.eq_one_of_zpow_mem {k : G} {Q : Set G} (hQ : IsCompact Q) (hk : ∀ j : ℤ, k ^ j ∈ Q) : Δ k = 1 := by sorry
