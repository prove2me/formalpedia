-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_pderiv_of_free
-- name    : Formalism.GM.ProjS.pderiv_of_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:38.732612+00:00
-- url     : https://prove2.me/theorems/b2228c66-e0a1-4ce2-8678-4fb5f7ad9cd0
-- title:
--   Proj S: pderiv of free
-- statement:
--   The Proj S construction uses the pderiv of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L511-L518
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L511-L518

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

theorem Formalism.GM.ProjS.pderiv_of_free (v : σ) (y : MvPolynomial σ k) (h : ∀ m ∈ y.support, m v = 0) : pderiv v y = 0 := by sorry
