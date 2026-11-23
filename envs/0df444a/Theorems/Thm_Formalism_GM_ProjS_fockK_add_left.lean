-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_add_left
-- name    : Formalism.GM.ProjS.fockK_add_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:28.105952+00:00
-- url     : https://prove2.me/theorems/8a0ac50c-afa8-4397-a742-0099a7b24ae1
-- title:
--   Proj S: fock K add left
-- statement:
--   The Proj S construction uses the fock K add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L33-L49

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

theorem Formalism.GM.ProjS.fockK_add_left (F F' G : MvPolynomial σ k) :
    M.fockK (F + F') G = M.fockK F G + M.fockK F' G := by sorry
