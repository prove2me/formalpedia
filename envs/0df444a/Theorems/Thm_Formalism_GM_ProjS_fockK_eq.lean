-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_eq
-- name    : Formalism.GM.ProjS.fockK_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:25.942421+00:00
-- url     : https://prove2.me/theorems/977cd3fa-ea81-4b3b-8d04-30096a4b1e35
-- title:
--   Proj S: fock K eq
-- statement:
--   The Proj S construction uses the fock K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L12-L13

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

theorem Formalism.GM.ProjS.fockK_eq (F G : MvPolynomial σ k) :
    M.fockK F G = ∑ m ∈ F.support, F.coeff m * G.coeff m * mfac m := by sorry
