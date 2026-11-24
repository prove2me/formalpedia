-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_mix_w
-- name    : Formalism.GM.ProjS.mix_w
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:14.372812+00:00
-- url     : https://prove2.me/theorems/f3e269b1-569b-4677-9f11-b518b9702994
-- title:
--   Proj S: mix w
-- statement:
--   The Proj S construction uses the mix w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L488-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L488-L489

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

theorem Formalism.GM.ProjS.mix_w (hv : M.TieVars w e zv sv) :
    ∀ c, ((∃ d, w d = w c) ∧ ∀ d, w d ≠ e c) ∨ ((∀ d, w d ≠ w c) ∧ ∃ d, w d = e c) := by sorry
