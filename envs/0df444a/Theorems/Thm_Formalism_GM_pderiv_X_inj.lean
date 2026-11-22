-- Prove2me | Theorems.Thm_Formalism_GM_pderiv_X_inj
-- name    : Formalism.GM.pderiv_X_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:25.112861+00:00
-- url     : https://prove2.me/theorems/9f6456b7-7960-4b77-8daf-b7922b6daf3a
-- title:
--   GM: pderiv X inj
-- statement:
--   The GM construction uses the pderiv X inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L76-L83

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

theorem Formalism.GM.pderiv_X_inj {f : Fin r → σ} (hf : Function.Injective f) (c d : Fin r) :
    pderiv (f c) (X (f d) : MvPolynomial σ k) = if d = c then 1 else 0 := by sorry
