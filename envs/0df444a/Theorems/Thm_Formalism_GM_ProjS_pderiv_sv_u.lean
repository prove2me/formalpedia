-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_pderiv_sv_u
-- name    : Formalism.GM.ProjS.pderiv_sv_u
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:18.992953+00:00
-- url     : https://prove2.me/theorems/78bc6b4b-ee3d-4b93-986e-9d8c08054b95
-- title:
--   Proj S: pderiv sv u
-- statement:
--   The Proj S construction uses the pderiv sv u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L567-L569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L567-L569

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
variable {o n z : ℕ} {y : MvPolynomial σ k}

theorem Formalism.GM.ProjS.pderiv_sv_u (hv : M.TieVars w e zv sv) (hz : M.ZSFree zv sv y) :
    pderiv sv (X zv ^ z * y) = 0 := by sorry
