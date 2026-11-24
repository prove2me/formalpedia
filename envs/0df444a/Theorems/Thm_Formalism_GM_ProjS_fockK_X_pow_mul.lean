-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_X_pow_mul
-- name    : Formalism.GM.ProjS.fockK_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:12.446428+00:00
-- url     : https://prove2.me/theorems/75515798-2654-4c74-b08f-ed1304e5c7ae
-- title:
--   Proj S: fock K X pow mul
-- statement:
--   The Proj S construction uses the fock K X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L390-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L390-L396

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

theorem Formalism.GM.ProjS.fockK_X_pow_mul (v : σ) (z : ℕ) (a h : MvPolynomial σ k) :
    M.fockK (X v ^ z * a) h = M.fockK a (((pderiv v).toLinearMap ^ z) h) := by sorry
