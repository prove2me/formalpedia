-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tv_e
-- name    : Formalism.GM.ProjS.tv_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:46.672797+00:00
-- url     : https://prove2.me/theorems/d3b579dc-bdf6-4abb-9757-e66b5437eecf
-- title:
--   Proj S: tv e
-- statement:
--   The Proj S construction uses the tv e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L455-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L455-L472

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

theorem Formalism.GM.ProjS.tv_e (hv : M.TieVars w e zv sv) : Function.Injective (Fin.cons sv e : Fin (r + 1) → σ) := by sorry
