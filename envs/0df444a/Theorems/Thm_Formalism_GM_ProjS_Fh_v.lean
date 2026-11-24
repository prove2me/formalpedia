-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_Fh_v
-- name    : Formalism.GM.ProjS.Fh_v
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:22.468357+00:00
-- url     : https://prove2.me/theorems/203c101e-f797-46b7-a9bd-273f8677c332
-- title:
--   Proj S: Fh v
-- statement:
--   The Proj S construction uses the Fh v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L571-L580
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L571-L580

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

theorem Formalism.GM.ProjS.Fh_v (hv : M.TieVars w e zv sv) (hz : M.ZSFree zv sv y) (l : ℕ) :
    tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ((tieF w e ^ l) (X zv ^ z * y)) =
      (tieF w e ^ (l + 1)) (X zv ^ z * y) := by sorry
