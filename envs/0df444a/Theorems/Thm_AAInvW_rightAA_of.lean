-- Prove2me | Theorems.Thm_AAInvW_rightAA_of
-- name    : AAInvW.rightAA_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:25:41.093357+00:00
-- url     : https://prove2.me/theorems/0613ba92-696b-4840-bf62-ab5b347212b9
-- title:
--   AAInv W: right AA of
-- statement:
--   The AAInv W construction uses the right AA of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdIntertwine.lean#L58-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdIntertwine.lean#L58-L123

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem AAInvW.rightAA_of (hM : OpModel) (hA : AlgAA) (hAv : AlgAAv) (hH : HpkInvol) (hUH : SsetUH)
    (hIC : SsetInvCol) (hRS : SsetRowStar) : RightAA := by sorry
