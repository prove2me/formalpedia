-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_X
-- name    : Formalism.GM.FrozenVariableLemmas.intPol_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:39.720693+00:00
-- url     : https://prove2.me/theorems/e950ae62-c0d9-4ebb-b07e-883c2199e0da
-- title:
--   Frozen Variable Lemmas: int Pol X
-- statement:
--   The Frozen Variable Lemmas construction uses the int Pol X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L217-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L217-L219

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

theorem Formalism.GM.FrozenVariableLemmas.intPol_X (x : τ) : (X x : MvPolynomial τ ℚ_[p]) ∈ M.IntPol p τ := by sorry
