-- Prove2me | Theorems.Thm_AAInvW_mRel_top
-- name    : AAInvW.mRel_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:22.854795+00:00
-- url     : https://prove2.me/theorems/1c2e94eb-536c-4a21-8de6-e9101469d35d
-- title:
--   AAInv W: m Rel top
-- statement:
--   The AAInv W construction uses the m Rel top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L91-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L91-L106

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

theorem AAInvW.mRel_top (hH : HInvol H) {G : Matrix (Fin n) (Fin n) ℂ → E} {ψ : mSub H E} (h : mRel G ψ)
    (v : ℂ) (a b : Fin n) : mRel (Formalism.QuantumDeterminants.Top (EabH H) v a b G) (Tm (mE hH) v a b ψ) := by sorry
