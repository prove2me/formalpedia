-- Prove2me | Theorems.Thm_AAInvW_ly_Top_left
-- name    : AAInvW.ly_Top_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:27:00.537824+00:00
-- url     : https://prove2.me/theorems/3282e2ef-65b0-4446-b69c-9bc1663811dc
-- title:
--   AAInv W: ly Top left
-- statement:
--   The AAInv W construction uses the ly Top left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/LyQminorLeft.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/LyQminorLeft.lean#L17-L22

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

theorem AAInvW.ly_Top_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E)
    (s : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.QuantumDeterminants.Top (EabH H) v a b (fun x => F (s * x)) = fun x => Formalism.QuantumDeterminants.Top (EabH H) v a b F (s * x) := by sorry
