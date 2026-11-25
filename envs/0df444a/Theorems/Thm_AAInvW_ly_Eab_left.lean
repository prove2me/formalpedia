-- Prove2me | Theorems.Thm_AAInvW_ly_Eab_left
-- name    : AAInvW.ly_Eab_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:17:27.304951+00:00
-- url     : https://prove2.me/theorems/78188b65-2e49-48c1-aa99-6cae3e979bba
-- title:
--   AAInv W: ly Eab left
-- statement:
--   The AAInv W construction uses the ly Eab left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/LyQminorLeft.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/LyQminorLeft.lean#L11-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_LyQminorLeft
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

theorem AAInvW.ly_Eab_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) (s : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b (fun x => F (s * x)) = fun x => EabH H a b F (s * x) := by sorry
