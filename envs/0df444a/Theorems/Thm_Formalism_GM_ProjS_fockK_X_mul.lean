-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_X_mul
-- name    : Formalism.GM.ProjS.fockK_X_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:41.282185+00:00
-- url     : https://prove2.me/theorems/6ca0d65d-ec5b-45b0-99ac-03eca8b430cf
-- title:
--   Proj S: fock K X mul
-- statement:
--   The Proj S construction uses the fock K X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L125-L130

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

theorem Formalism.GM.ProjS.fockK_X_mul (v : σ) (g h : MvPolynomial σ k) :
    M.fockK (X v * g) h = M.fockK g (pderiv v h) := by sorry
