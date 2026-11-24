-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_pderiv_pow_X_pow_mul
-- name    : Formalism.GM.ProjS.pderiv_pow_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:17.654739+00:00
-- url     : https://prove2.me/theorems/5dec8180-9b6c-4348-b336-9ed9bd5dfa2b
-- title:
--   Proj S: pderiv pow X pow mul
-- statement:
--   The Proj S construction uses the pderiv pow X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L403-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L403-L412

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

theorem Formalism.GM.ProjS.pderiv_pow_X_pow_mul (v : σ) (b : MvPolynomial σ k) (hb : pderiv v b = 0) (z : ℕ) :
    ((pderiv v).toLinearMap ^ z) (X v ^ z * b) = (z.factorial : k) • b := by sorry
