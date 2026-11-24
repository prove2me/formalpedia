-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_mfac_add_single
-- name    : Formalism.GM.ProjS.mfac_add_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:17.487455+00:00
-- url     : https://prove2.me/theorems/5f9e5301-80c9-44d4-b035-91bd612cc974
-- title:
--   Proj S: mfac add single
-- statement:
--   The Proj S construction uses the mfac add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L89-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L89-L116

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

theorem Formalism.GM.ProjS.mfac_add_single (m : σ →₀ ℕ) (v : σ) :
    (mfac (m + Finsupp.single v 1) : k) = mfac m * ((m v : k) + 1) := by sorry
