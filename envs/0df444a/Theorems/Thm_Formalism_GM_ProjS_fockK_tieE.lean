-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_tieE
-- name    : Formalism.GM.ProjS.fockK_tieE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:27.316849+00:00
-- url     : https://prove2.me/theorems/d4b3fc43-bc19-4f5a-8fe0-8385c12abba3
-- title:
--   Proj S: fock K tie E
-- statement:
--   The Proj S construction uses the fock K tie E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L372-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L372-L376

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

theorem Formalism.GM.ProjS.fockK_tieE {r : ℕ} (w e : Fin r → σ) (g h : MvPolynomial σ k) :
    M.fockK (tieE w e g) h = M.fockK g (tieF w e h) := by sorry
