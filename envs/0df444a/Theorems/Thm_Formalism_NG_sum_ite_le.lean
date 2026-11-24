-- Prove2me | Theorems.Thm_Formalism_NG_sum_ite_le
-- name    : Formalism.NG.sum_ite_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:52.037006+00:00
-- url     : https://prove2.me/theorems/2911efa5-a50f-4aa6-8982-d452596f4287
-- title:
--   NG: sum ite le
-- statement:
--   The NG construction uses the sum ite le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SumIteLe.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SumIteLe.lean#L11-L27

import Definitions.Def_Formalism_CharacterColumnKernels_StatementNG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SumIteLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG

theorem Formalism.NG.sum_ite_le (t : ℕ) (vhE : ℕ∞) (Sha : ℕ → ℕ∞) :
    ∑ i ∈ range t, (if i + 1 = 1 then vhE else Sha (i + 1 - 1)) ≤
      vhE + ∑ e ∈ Ioo 0 t, Sha e := by sorry
