-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_JacobianCoordinates_JL_HaarCore_pull
-- name    : Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:09.851336+00:00
-- url     : https://prove2.me/theorems/a24a8adb-62c2-4e55-818c-d5d91b00633a
-- title:
--   Haar Core: pull
-- statement:
--   The Haar Core construction uses the pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SigmaFiniteOfFcG.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SigmaFiniteOfFcG.lean#L20-L43

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SigmaFiniteOfFcG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.pull (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G) (hνc : ν (S : Set G)ᶜ = 0)
    (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) (hνf : IsFiniteMeasureOnCompacts ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (ν.comap (Subtype.val : S → G)) ∧
      (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by sorry
