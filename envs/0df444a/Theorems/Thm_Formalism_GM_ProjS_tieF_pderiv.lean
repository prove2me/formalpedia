-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tieF_pderiv
-- name    : Formalism.GM.ProjS.tieF_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:26.339092+00:00
-- url     : https://prove2.me/theorems/60153d38-c771-4e87-b46b-577f99f01689
-- title:
--   Proj S: tie F pderiv
-- statement:
--   The Proj S construction uses the tie F pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L260-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L260-L264

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

theorem Formalism.GM.ProjS.tieF_pderiv {r : ℕ} (w e : Fin r → σ) (v : σ) (g : MvPolynomial σ k) :
    tieF w e (pderiv v g) = pderiv v (tieF w e g) := by sorry
