-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freezeSub_int
-- name    : Formalism.GM.FrozenVariableLemmas.freezeSub_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:38.726251+00:00
-- url     : https://prove2.me/theorems/296dd179-2fa5-4d73-b3de-544e1c04e455
-- title:
--   Frozen Variable Lemmas: freeze Sub int
-- statement:
--   The Frozen Variable Lemmas construction uses the freeze Sub int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L243-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L243-L252

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

theorem Formalism.GM.FrozenVariableLemmas.freezeSub_int (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r)
    (x : Fin N × Fin r) : M.freezeSub p LL ρ x ∈ M.IntPol p (Fin (N + 1) × Fin r) := by sorry
