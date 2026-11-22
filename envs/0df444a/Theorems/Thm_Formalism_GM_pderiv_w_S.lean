-- Prove2me | Theorems.Thm_Formalism_GM_pderiv_w_S
-- name    : Formalism.GM.pderiv_w_S
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:02:19.304863+00:00
-- url     : https://prove2.me/theorems/a1e2751b-69e0-46db-846e-5c82b81cf3e0
-- title:
--   GM: pderiv w S
-- statement:
--   The GM construction uses the pderiv w S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L92-L98

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
variable {w e}

theorem Formalism.GM.pderiv_w_S (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d)
    (c : Fin r) : pderiv (w c) (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = X (e c) := by sorry
