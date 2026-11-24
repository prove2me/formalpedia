-- Prove2me | Theorems.Thm_AAInvW_inUH_mul
-- name    : AAInvW.inUH_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:17.142125+00:00
-- url     : https://prove2.me/theorems/251e9919-f21b-4415-a3d4-899ad65ae0aa
-- title:
--   AAInv W: in UH mul
-- statement:
--   The AAInv W construction uses the in UH mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorsCommuteTranslationsOfLeftRight.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorsCommuteTranslationsOfLeftRight.lean#L11-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorsCommuteTranslationsOfLeftRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem AAInvW.inUH_mul {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) :
    inUH H (a * b) := by sorry
