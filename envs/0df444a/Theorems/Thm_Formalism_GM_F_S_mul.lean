-- Prove2me | Theorems.Thm_Formalism_GM_F_S_mul
-- name    : Formalism.GM.F_S_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:08.379955+00:00
-- url     : https://prove2.me/theorems/0fb58d9f-665a-450a-aef3-c3fbe38f8ee5
-- title:
--   GM: F S mul
-- statement:
--   The GM construction uses the F S mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L104-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L104-L136

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

theorem Formalism.GM.F_S_mul (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (a b : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g)
    (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) :
    ∑ c, pderiv (w c) (pderiv (e c) ((∑ d, X (w d) * X (e d)) * g)) =
      (∑ d, X (w d) * X (e d)) * ∑ c, pderiv (w c) (pderiv (e c) g) + ((a + b + r : ℕ) : k) • g := by sorry
