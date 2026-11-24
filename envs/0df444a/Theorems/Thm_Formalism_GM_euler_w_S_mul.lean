-- Prove2me | Theorems.Thm_Formalism_GM_euler_w_S_mul
-- name    : Formalism.GM.euler_w_S_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:25.335536+00:00
-- url     : https://prove2.me/theorems/e940d9f8-121c-4a7f-93c0-ecd6dcd0a104
-- title:
--   GM: euler w S mul
-- statement:
--   The GM construction uses the euler w S mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L138-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L138-L150

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

theorem Formalism.GM.euler_w_S_mul (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (a : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g) :
    ∑ c, X (w c) * pderiv (w c) ((∑ d, X (w d) * X (e d)) * g) =
      ((a + 1 : ℕ) : k) • ((∑ d, X (w d) * X (e d)) * g) := by sorry
