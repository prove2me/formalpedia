-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_pderiv_comm
-- name    : Formalism.GM.ProjS.pderiv_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:41.959893+00:00
-- url     : https://prove2.me/theorems/fda8f33b-9d02-4987-a93d-35aa68e62468
-- title:
--   Proj S: pderiv comm
-- statement:
--   The Proj S construction uses the pderiv comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L143-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L143-L159

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
variable {k σ : Type} [Field k]

theorem Formalism.GM.ProjS.pderiv_comm (i j : σ) (p : MvPolynomial σ k) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by sorry
