-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eulL_pderiv_notMem
-- name    : Formalism.GM.ProjS.eulL_pderiv_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:58.911863+00:00
-- url     : https://prove2.me/theorems/05302ae2-bc99-4df8-8638-7f20e46243a3
-- title:
--   Proj S: eul L pderiv not Mem
-- statement:
--   The Proj S construction uses the eul L pderiv not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L212-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L212-L216

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

theorem Formalism.GM.ProjS.eulL_pderiv_notMem {s : ℕ} (t : Fin s → σ) (v : σ) (hv : ∀ c, t c ≠ v) (h : MvPolynomial σ k) :
    eulL t (pderiv v h) = pderiv v (eulL t h) := by sorry
