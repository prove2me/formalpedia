-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Weil_QuotInt_measurable_mulH
-- name    : Formalism.L2.SG.Pf.Weil.QuotInt.measurable_mulH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:05.400804+00:00
-- url     : https://prove2.me/theorems/50823635-9c6c-4b5f-83b6-e05ec172b5df
-- title:
--   Quot Int: measurable mul H
-- statement:
--   The Quot Int construction uses the measurable mul H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CasimirReductionTheory/OneParameterDerivatives/WeilIndicatorMeasures/MeasurableUnitMulIndicator.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CasimirReductionTheory/OneParameterDerivatives/WeilIndicatorMeasures/MeasurableUnitMulIndicator.lean#L14-L15

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Weil
open Formalism.L2.SG.Pf.Weil.QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] {H : Subgroup G}

theorem Formalism.L2.SG.Pf.Weil.QuotInt.measurable_mulH : Measurable (fun p : G × H => p.1 * (p.2 : G)) := by sorry
