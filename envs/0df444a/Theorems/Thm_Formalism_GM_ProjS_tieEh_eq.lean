-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tieEh_eq
-- name    : Formalism.GM.ProjS.tieEh_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:47.732963+00:00
-- url     : https://prove2.me/theorems/520141b6-4365-4745-9c17-09af05e5d453
-- title:
--   Proj S: tie Eh eq
-- statement:
--   The Proj S construction uses the tie Eh eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L414-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L414-L419

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

theorem Formalism.GM.ProjS.tieEh_eq {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    (M.tieEh w e zv sv : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) =
      tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) := by sorry
