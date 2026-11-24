-- Prove2me | Theorems.Thm_AAInvW_lx_mulVec_apply
-- name    : AAInvW.lx_mulVec_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:44.432907+00:00
-- url     : https://prove2.me/theorems/fe3977e9-d723-4da4-a582-a9ae7638be22
-- title:
--   AAInv W: lx mul Vec apply
-- statement:
--   The AAInv W construction uses the lx mul Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L17-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
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

theorem AAInvW.lx_mulVec_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    (M *ᵥ v) i = ∑ j, M i j * v j := by sorry
