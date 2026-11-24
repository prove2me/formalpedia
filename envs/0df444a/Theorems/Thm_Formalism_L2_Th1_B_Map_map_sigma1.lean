-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Map_map_sigma1
-- name    : Formalism.L2.Th1.B.Map.map_sigma1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:46.387913+00:00
-- url     : https://prove2.me/theorems/1d76ec27-7f48-4b80-bb77-726fd7dd9c47
-- title:
--   Map: map sigma1
-- statement:
--   The Map construction uses the map sigma1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L109-L112

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

theorem Formalism.L2.Th1.B.Map.map_sigma1 (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigma1 e1 kap w) = sigma1 (j e1) (j kap) (PowerSeries.map j w) := by sorry
