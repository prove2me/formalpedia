-- Prove2me | Theorems.Thm_Formalism_GM_pderiv_e_S
-- name    : Formalism.GM.pderiv_e_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:02:18.99651+00:00
-- url     : https://prove2.me/theorems/e993f41f-d236-4567-976c-df23e9d70720
-- title:
--   GM: pderiv e S
-- statement:
--   The GM construction uses the pderiv e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L85-L90

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

theorem Formalism.GM.pderiv_e_S (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (c : Fin r) : pderiv (e c) (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = X (w c) := by sorry
