-- Prove2me | Theorems.Thm_AAInvW_lx_det_tri
-- name    : AAInvW.lx_det_tri
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:53.03352+00:00
-- url     : https://prove2.me/theorems/34c4b44e-cff5-46f2-93e3-5b8ed945d612
-- title:
--   AAInv W: lx det tri
-- statement:
--   The AAInv W construction uses the lx det tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L11-L15

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

theorem AAInvW.lx_det_tri {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (hT : ∀ a b : Fin m, a < b → T a b = 0)
    (hd : ∀ a, T a a = 1) : (T * N).det = N.det := by sorry
