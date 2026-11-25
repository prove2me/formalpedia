-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_translate_props
-- name    : Formalism.L2.S.Pv.EnergyAbs.translate_props
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:20.991717+00:00
-- url     : https://prove2.me/theorems/b116a953-8f99-4c30-aa2a-a99b99add428
-- title:
--   Energy Abs: translate props
-- statement:
--   The Energy Abs construction uses the translate props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsPoint.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsPoint.lean#L39-L48

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTail
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsLower
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEquiv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem Formalism.L2.S.Pv.EnergyAbs.translate_props {μS : Measure G} {S : Set G} (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω)
    (hΩS : Ω ⊆ S) (hΩt : μS Ω < ⊤) {s : G} (hs : s ∈ S) :
    MeasurableSet ((fun v => v * s⁻¹) ⁻¹' Ω) ∧ (fun v => v * s⁻¹) ⁻¹' Ω ⊆ S ∧
      μS ((fun v => v * s⁻¹) ⁻¹' Ω) < ⊤ := by sorry
