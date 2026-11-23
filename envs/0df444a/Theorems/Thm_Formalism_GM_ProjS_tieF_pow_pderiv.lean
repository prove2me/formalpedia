-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tieF_pow_pderiv
-- name    : Formalism.GM.ProjS.tieF_pow_pderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:32.163315+00:00
-- url     : https://prove2.me/theorems/6ed72a6e-0d3b-4485-9910-6997def5b049
-- title:
--   Proj S: tie F pow pderiv
-- statement:
--   The Proj S construction uses the tie F pow pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L266-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L266-L272

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

theorem Formalism.GM.ProjS.tieF_pow_pderiv {r : ℕ} (w e : Fin r → σ) (v : σ) (g : MvPolynomial σ k) (l : ℕ) :
    (tieF w e ^ l) (pderiv v g) = pderiv v ((tieF w e ^ l) g) := by sorry
