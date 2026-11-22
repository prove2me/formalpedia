-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_symm
-- name    : Formalism.GM.ProjS.fockK_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:07.829807+00:00
-- url     : https://prove2.me/theorems/3e68a4df-4550-4eac-89df-72a300039dcb
-- title:
--   Proj S: fock K symm
-- statement:
--   The Proj S construction uses the fock K symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L27-L31

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

theorem Formalism.GM.ProjS.fockK_symm (F G : MvPolynomial σ k) : M.fockK F G = M.fockK G F := by sorry
