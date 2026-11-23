-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_pow
-- name    : Formalism.GM.FrozenVariableLemmas.intPol_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:46.513782+00:00
-- url     : https://prove2.me/theorems/640472e4-ff5b-4426-a904-99cfd39932e8
-- title:
--   Frozen Variable Lemmas: int Pol pow
-- statement:
--   The Frozen Variable Lemmas construction uses the int Pol pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L221-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L221-L225

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

theorem Formalism.GM.FrozenVariableLemmas.intPol_pow {F : MvPolynomial τ ℚ_[p]} (hF : F ∈ M.IntPol p τ) (k : ℕ) :
    F ^ k ∈ M.IntPol p τ := by sorry
