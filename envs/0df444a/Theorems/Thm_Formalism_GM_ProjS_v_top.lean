-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_v_top
-- name    : Formalism.GM.ProjS.v_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:25.307155+00:00
-- url     : https://prove2.me/theorems/e5e446ed-f748-43e8-b34b-3c8c0e0728b3
-- title:
--   Proj S: v top
-- statement:
--   The Proj S construction uses the v top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L602-L605
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L602-L605

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
variable {o n z : ℕ} {y : MvPolynomial σ k}

theorem Formalism.GM.ProjS.v_top [CharZero k] (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) :
    (tieF w e ^ (o + 1)) (X zv ^ z * y) = 0 := by sorry
