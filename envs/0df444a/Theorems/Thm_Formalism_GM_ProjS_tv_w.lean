-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tv_w
-- name    : Formalism.GM.ProjS.tv_w
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:37.462919+00:00
-- url     : https://prove2.me/theorems/58bfdac1-3945-49c9-a2ba-9820e13a30e8
-- title:
--   Proj S: tv w
-- statement:
--   The Proj S construction uses the tv w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L436-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L436-L453

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

theorem Formalism.GM.ProjS.tv_w (hv : M.TieVars w e zv sv) : Function.Injective (Fin.cons zv w : Fin (r + 1) → σ) := by sorry
