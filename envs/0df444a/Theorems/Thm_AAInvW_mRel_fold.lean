-- Prove2me | Theorems.Thm_AAInvW_mRel_fold
-- name    : AAInvW.mRel_fold
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:44.385408+00:00
-- url     : https://prove2.me/theorems/66fdd98c-9ece-419c-bc94-18a3a9542e47
-- title:
--   AAInv W: m Rel fold
-- statement:
--   The AAInv W construction uses the m Rel fold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L108-L116

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

theorem AAInvW.mRel_fold (hH : HInvol H) (l : List (Fin n × Fin n × ℂ)) {f : Matrix (Fin n) (Fin n) ℂ → E}
    {ψ : mSub H E} (h : mRel f ψ) :
    mRel ((l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.2.2 p.1 p.2.1).foldr (fun T h => T h) f)
      ((l.map fun p => Tm (mE hH) p.2.2 p.1 p.2.1).prod ψ) := by sorry
