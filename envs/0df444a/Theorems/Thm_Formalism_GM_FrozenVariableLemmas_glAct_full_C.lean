-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_C
-- name    : Formalism.GM.FrozenVariableLemmas.glAct_full_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:37.35415+00:00
-- url     : https://prove2.me/theorems/5a09094d-b7f0-4ae5-af89-fa7ee71a3a14
-- title:
--   Frozen Variable Lemmas: gl Act full C
-- statement:
--   The Frozen Variable Lemmas construction uses the gl Act full C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L122-L124

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
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} (L : M.Letters K) (c ρ : Fin r)

theorem Formalism.GM.FrozenVariableLemmas.glAct_full_C (a : ℚ_[p]) : M.glAct p L K c ρ (C a) = 0 := by sorry
