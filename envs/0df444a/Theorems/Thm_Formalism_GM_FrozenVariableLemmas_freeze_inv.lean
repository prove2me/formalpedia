-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freeze_inv
-- name    : Formalism.GM.FrozenVariableLemmas.freeze_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:35.791104+00:00
-- url     : https://prove2.me/theorems/c3d174cc-c1cd-4d64-a5d7-70a904524e0e
-- title:
--   Frozen Variable Lemmas: freeze inv
-- statement:
--   The Frozen Variable Lemmas construction uses the freeze inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L164-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L164-L193

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

theorem Formalism.GM.FrozenVariableLemmas.freeze_inv (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : M.IsFrozenInv p LL ρ n (M.freeze p LL ρ n f) := by sorry
