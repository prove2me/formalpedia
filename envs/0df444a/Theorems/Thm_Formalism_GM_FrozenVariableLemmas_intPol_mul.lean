-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_mul
-- name    : Formalism.GM.FrozenVariableLemmas.intPol_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:13.876472+00:00
-- url     : https://prove2.me/theorems/a0ffbce6-e929-49e0-a8ee-9f8f60c347a4
-- title:
--   Frozen Variable Lemmas: int Pol mul
-- statement:
--   The Frozen Variable Lemmas construction uses the int Pol mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L210-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L210-L215

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {τ : Type}

theorem Formalism.GM.FrozenVariableLemmas.intPol_mul {F G : MvPolynomial τ ℚ_[p]} (hF : F ∈ M.IntPol p τ) (hG : G ∈ M.IntPol p τ) :
    F * G ∈ M.IntPol p τ := by sorry
