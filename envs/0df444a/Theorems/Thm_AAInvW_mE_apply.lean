-- Prove2me | Theorems.Thm_AAInvW_mE_apply
-- name    : AAInvW.mE_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:34:48.631749+00:00
-- url     : https://prove2.me/theorems/60fb1770-580c-4da8-8224-bea2d5e24545
-- title:
--   AAInv W: m E apply
-- statement:
--   The AAInv W construction uses the m E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L72-L74

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
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
open scoped Classical
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

theorem AAInvW.mE_apply (hH : HInvol H) (a b : Fin n) (φ : mSub H E) (x : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x}) :
    ((mE hH a b φ : mSub H E) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) x =
      EabH H a b (mExt φ.1) x.1 := by sorry
