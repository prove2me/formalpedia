-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_X
-- name    : Formalism.GM.FrozenVariableLemmas.glAct_full_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:39.060422+00:00
-- url     : https://prove2.me/theorems/8c0a8b22-16c1-4659-ab81-0053a706f2b9
-- title:
--   Frozen Variable Lemmas: gl Act full X
-- statement:
--   The Frozen Variable Lemmas construction uses the gl Act full X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L126-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L126-L136

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

theorem Formalism.GM.FrozenVariableLemmas.glAct_full_X (b : Fin K) (d : Fin r) :
    M.glAct p L K c ρ (X (b, d)) =
      if L.vec b then (if d = ρ then X (b, c) else 0) else (if d = c then -X (b, ρ) else 0) := by sorry
