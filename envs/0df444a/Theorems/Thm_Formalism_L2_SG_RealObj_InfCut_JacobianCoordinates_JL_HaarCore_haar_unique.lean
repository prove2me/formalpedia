-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_JacobianCoordinates_JL_HaarCore_haar_unique
-- name    : Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.haar_unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:33.407469+00:00
-- url     : https://prove2.me/theorems/2a5ee677-49c0-457a-ad25-976d4da57376
-- title:
--   Haar Core: haar unique
-- statement:
--   The Haar Core construction uses the haar unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SigmaFiniteOfFcG.lean#L45-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SigmaFiniteOfFcG.lean#L45-L68

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

theorem Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.haar_unique (S : Subgroup G) (hS : IsClosed (S : Set G)) (μ m : Measure G) (hμ0 : μ ≠ 0)
    (hμc : μ (S : Set G)ᶜ = 0) (hμi : ∀ s ∈ S, μ.map (fun x => s * x) = μ) (hμf : IsFiniteMeasureOnCompacts μ)
    (hmc : m (S : Set G)ᶜ = 0) (hmi : ∀ s ∈ S, m.map (fun x => s * x) = m) (hmf : IsFiniteMeasureOnCompacts m) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ m = c • μ := by sorry
