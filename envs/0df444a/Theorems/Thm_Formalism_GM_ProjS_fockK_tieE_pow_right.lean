-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_tieE_pow_right
-- name    : Formalism.GM.ProjS.fockK_tieE_pow_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:30.084927+00:00
-- url     : https://prove2.me/theorems/aebb561a-de22-4077-a178-079322ea13f9
-- title:
--   Proj S: fock K tie E pow right
-- statement:
--   The Proj S construction uses the fock K tie E pow right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L386-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L386-L388

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

theorem Formalism.GM.ProjS.fockK_tieE_pow_right {r : ℕ} (w e : Fin r → σ) (l : ℕ) (g h : MvPolynomial σ k) :
    M.fockK g ((tieE w e ^ l) h) = M.fockK ((tieF w e ^ l) g) h := by sorry
