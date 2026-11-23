-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_weight_fst
-- name    : Formalism.GM.FrozenVariableLemmas.weight_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:53.808103+00:00
-- url     : https://prove2.me/theorems/11795fc0-9bf0-46f8-9ec6-5a7eeaf9fd97
-- title:
--   Frozen Variable Lemmas: weight fst
-- statement:
--   The Frozen Variable Lemmas construction uses the weight fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L21-L27

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

theorem Formalism.GM.FrozenVariableLemmas.weight_fst {M r : ℕ} (G : Fin M → ℕ) (m : Fin M × Fin r →₀ ℕ) :
    Finsupp.weight (fun x : Fin M × Fin r => G x.1) m = ∑ b, G b * ∑ c, m (b, c) := by sorry
