-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tieFh_eq
-- name    : Formalism.GM.ProjS.tieFh_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:15.491806+00:00
-- url     : https://prove2.me/theorems/2ac5a24a-12bb-4c88-a33c-503705e213e0
-- title:
--   Proj S: tie Fh eq
-- statement:
--   The Proj S construction uses the tie Fh eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L421-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L421-L426

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

theorem Formalism.GM.ProjS.tieFh_eq {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    (M.tieFh w e zv sv : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) =
      tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) := by sorry
