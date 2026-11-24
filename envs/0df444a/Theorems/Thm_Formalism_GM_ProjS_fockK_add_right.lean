-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_add_right
-- name    : Formalism.GM.ProjS.fockK_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:37.566461+00:00
-- url     : https://prove2.me/theorems/ef4f2251-5116-4ed6-896f-6694e2450a36
-- title:
--   Proj S: fock K add right
-- statement:
--   The Proj S construction uses the fock K add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L73-L75

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

theorem Formalism.GM.ProjS.fockK_add_right (F G G' : MvPolynomial σ k) :
    M.fockK F (G + G') = M.fockK F G + M.fockK F G' := by sorry
