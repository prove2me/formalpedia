-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fh_P
-- name    : Formalism.GM.ProjS.fh_P
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:23.780243+00:00
-- url     : https://prove2.me/theorems/93bf7418-3033-4be6-b63b-99dd59689ced
-- title:
--   Proj S: fh P
-- statement:
--   The Proj S construction uses the fh P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L704-L735
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L704-L735

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

theorem Formalism.GM.ProjS.fh_P [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) :
    tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) (M.tieP w e zv sv o n z y) = 0 := by sorry
