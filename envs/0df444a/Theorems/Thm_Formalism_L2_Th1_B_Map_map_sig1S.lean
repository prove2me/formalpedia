-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Map_map_sig1S
-- name    : Formalism.L2.Th1.B.Map.map_sig1S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:44.516825+00:00
-- url     : https://prove2.me/theorems/5ef1a6c7-64d3-47c5-8dc5-f9cfd4c9d9fb
-- title:
--   Map: map sig1 S
-- statement:
--   The Map construction uses the map sig1 S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L84-L88

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')

theorem Formalism.L2.Th1.B.Map.map_sig1S (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigmaOneSeries e1 kap w) = sigmaOneSeries (j e1) (j kap) (PowerSeries.map j w) := by sorry
