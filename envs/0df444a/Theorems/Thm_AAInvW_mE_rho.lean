-- Prove2me | Theorems.Thm_AAInvW_mE_rho
-- name    : AAInvW.mE_rho
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:36.141125+00:00
-- url     : https://prove2.me/theorems/3a1c3e24-219a-4e02-a70a-b56d148852e1
-- title:
--   AAInv W: m E rho
-- statement:
--   The AAInv W construction uses the m E rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L143-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean#L143-L155

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

theorem AAInvW.mE_rho (hH : HInvol H) (s : Matrix (Fin n) (Fin n) ℂ) (hs : inUH H s) (a b : Fin n) :
    mE (E := E) hH a b * mRho hH s hs = mRho hH s hs * ∑ c, ∑ d, (s⁻¹ c a * s b d) • mE hH c d := by sorry
