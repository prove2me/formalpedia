-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_smul_right
-- name    : Formalism.GM.ProjS.fockK_smul_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:44.442807+00:00
-- url     : https://prove2.me/theorems/12a76f0e-4e58-4a8a-9c3f-433db3dc6105
-- title:
--   Proj S: fock K smul right
-- statement:
--   The Proj S construction uses the fock K smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L77-L79

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

theorem Formalism.GM.ProjS.fockK_smul_right (c : k) (F G : MvPolynomial σ k) :
    M.fockK F (c • G) = c * M.fockK F G := by sorry
