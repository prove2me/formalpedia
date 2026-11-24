-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_Fh_pow_u
-- name    : Formalism.GM.ProjS.Fh_pow_u
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:00.584082+00:00
-- url     : https://prove2.me/theorems/c5f9ab69-e184-4969-8c93-24908be7b26f
-- title:
--   Proj S: Fh pow u
-- statement:
--   The Proj S construction uses the Fh pow u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L582-L589
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L582-L589

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

theorem Formalism.GM.ProjS.Fh_pow_u (hv : M.TieVars w e zv sv) (hz : M.ZSFree zv sv y) (l : ℕ) :
    (tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l) (X zv ^ z * y) =
      (tieF w e ^ l) (X zv ^ z * y) := by sorry
