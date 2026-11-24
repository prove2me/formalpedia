-- Prove2me | Theorems.Thm_Formalism_GM_euler_e_S_mul
-- name    : Formalism.GM.euler_e_S_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:22.255092+00:00
-- url     : https://prove2.me/theorems/46f73c9a-f5e9-4fa7-a5cf-f2519945dc16
-- title:
--   GM: euler e S mul
-- statement:
--   The GM construction uses the euler e S mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L152-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L152-L164

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

theorem Formalism.GM.euler_e_S_mul (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (b : ℕ) (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) :
    ∑ c, X (e c) * pderiv (e c) ((∑ d, X (w d) * X (e d)) * g) =
      ((b + 1 : ℕ) : k) • ((∑ d, X (w d) * X (e d)) * g) := by sorry
