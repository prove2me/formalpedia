-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_cnt_measurable
-- name    : Formalism.L2.S.Pv.EnergyAbs.cnt_measurable
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:05.192843+00:00
-- url     : https://prove2.me/theorems/0860e331-d1ac-494f-be9b-b3ec8948993a
-- title:
--   Energy Abs: cnt measurable
-- statement:
--   The Energy Abs construction uses the cnt measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolnerConv.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolnerConv.lean#L19-L23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem Formalism.L2.S.Pv.EnergyAbs.cnt_measurable {μS : Measure G} [SFinite μS] {Ω : Set G} (hΩ : MeasurableSet Ω) :
    Measurable (cnt μS Ω) := by sorry
