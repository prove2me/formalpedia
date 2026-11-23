-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eulL_pderiv_mem
-- name    : Formalism.GM.ProjS.eulL_pderiv_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:57.345282+00:00
-- url     : https://prove2.me/theorems/e80c29ae-50be-49fe-b897-83ae170d7800
-- title:
--   Proj S: eul L pderiv mem
-- statement:
--   The Proj S construction uses the eul L pderiv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L218-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L218-L231

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

theorem Formalism.GM.ProjS.eulL_pderiv_mem {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (c0 : Fin s)
    (h : MvPolynomial σ k) :
    eulL t (pderiv (t c0) h) = pderiv (t c0) (eulL t h) - pderiv (t c0) h := by sorry
