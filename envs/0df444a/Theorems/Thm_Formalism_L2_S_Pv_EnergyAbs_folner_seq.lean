-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_folner_seq
-- name    : Formalism.L2.S.Pv.EnergyAbs.folner_seq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:54.01922+00:00
-- url     : https://prove2.me/theorems/7440d080-6adb-5f99-a449-3b50a6b82984
-- title:
--   Energy Abs: folner seq
-- statement:
--   The Energy Abs construction uses the folner seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolner.lean#L29-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolner.lean#L29-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerSum
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem Formalism.L2.S.Pv.EnergyAbs.folner_seq [LocallyCompactSpace G] [SecondCountableTopology G] {S : Set G} {μS : Measure G}
    (hS : IsHaarSub S μS) (hF : IsFolner S μS) :
    ∃ Ω : ℕ → Set G, (∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤) ∧
      ∀ K : Set G, IsCompact K → K ⊆ S →
        Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1) := by sorry
