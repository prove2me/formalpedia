-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freezeSub_isWH
-- name    : Formalism.GM.FrozenVariableLemmas.freezeSub_isWH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:35.146807+00:00
-- url     : https://prove2.me/theorems/0e2321f6-f051-4dc6-9fff-3a50fde3be76
-- title:
--   Frozen Variable Lemmas: freeze Sub is WH
-- statement:
--   The Frozen Variable Lemmas construction uses the freeze Sub is WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L38-L51

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

theorem Formalism.GM.FrozenVariableLemmas.freezeSub_isWH (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r)
    (g : Fin (N + 1) → ℕ) (x : Fin N × Fin r) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => g y.1) (M.freezeSub p LL ρ x)
      (g (Fin.castSucc x.1) + g (Fin.last N)) := by sorry
