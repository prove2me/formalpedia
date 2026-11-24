-- Prove2me | Theorems.Thm_Formalism_GM_euler_pow
-- name    : Formalism.GM.euler_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:24.634084+00:00
-- url     : https://prove2.me/theorems/4f7a4cb5-3d67-4f92-84da-7efab4c9f38e
-- title:
--   GM: euler pow
-- statement:
--   The GM construction uses the euler pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L178-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L178-L191

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

theorem Formalism.GM.euler_pow (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (u : MvPolynomial σ k) (a b : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) u = (a : k) • u)
    (hE : ∑ c, X (e c) * pderiv (e c) u = (b : k) • u) (j : ℕ) :
    (∑ c, X (w c) * pderiv (w c) ((tieE w e ^ j) u) = ((a + j : ℕ) : k) • (tieE w e ^ j) u) ∧
    (∑ c, X (e c) * pderiv (e c) ((tieE w e ^ j) u) = ((b + j : ℕ) : k) • (tieE w e ^ j) u) := by sorry
