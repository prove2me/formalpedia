-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_measure_inv_preimage
-- name    : Formalism.L2.S.Pv.EnergyAbs.measure_inv_preimage
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:24:59.036539+00:00
-- url     : https://prove2.me/theorems/86b419b5-55cf-4960-96c7-0c54cb18319f
-- title:
--   Energy Abs: measure inv preimage
-- statement:
--   The Energy Abs construction uses the measure inv preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsLower.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsLower.lean#L31-L37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsLower
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
open MeasureTheory Measure Filter Topology
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]

theorem Formalism.L2.S.Pv.EnergyAbs.measure_inv_preimage {μS : Measure G} [MeasurableInv G] (hinv : μS.map (fun x => x⁻¹) = μS)
    (B : Set G) : μS {s | s⁻¹ ∈ B} = μS B := by sorry
