-- Prove2me | Theorems.Thm_AAInvW_mQminor
-- name    : AAInvW.mQminor
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:25.552045+00:00
-- url     : https://prove2.me/theorems/0733c599-dab8-4541-a9cc-3c3eb2971fd1
-- title:
--   AAInv W: m Qminor
-- statement:
--   The AAInv W construction uses the m Qminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L118-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L118-L133

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

theorem AAInvW.mQminor (hH : HInvol H) (t : ℕ) (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUH H g) (hf : SmoothOnH H f) :
    qminorOp (EabH H) a b u f g =
      ((qminor (mE hH) a b u (mCls f) : mSub H E) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨g, hg⟩ := by sorry
