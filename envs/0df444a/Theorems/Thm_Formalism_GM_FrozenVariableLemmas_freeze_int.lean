-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freeze_int
-- name    : Formalism.GM.FrozenVariableLemmas.freeze_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:39.70728+00:00
-- url     : https://prove2.me/theorems/e71a6e9f-8e4d-4676-aee0-c9b84c3a6065
-- title:
--   Frozen Variable Lemmas: freeze int
-- statement:
--   The Frozen Variable Lemmas construction uses the freeze int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L254-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L254-L257

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

theorem Formalism.GM.FrozenVariableLemmas.freeze_int (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.IntPol p (Fin N × Fin r)) :
    M.freeze p LL ρ n f ∈ M.IntPol p (Fin (N + 1) × Fin r) := by sorry
