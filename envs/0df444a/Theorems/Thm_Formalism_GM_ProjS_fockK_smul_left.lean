-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_smul_left
-- name    : Formalism.GM.ProjS.fockK_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:44.886734+00:00
-- url     : https://prove2.me/theorems/6e46639b-fdde-4e61-9dc4-0de8bc5a0c24
-- title:
--   Proj S: fock K smul left
-- statement:
--   The Proj S construction uses the fock K smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L51-L61

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

theorem Formalism.GM.ProjS.fockK_smul_left (c : k) (F G : MvPolynomial σ k) :
    M.fockK (c • F) G = c * M.fockK F G := by sorry
