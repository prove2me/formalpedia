-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eulL_of_support
-- name    : Formalism.GM.ProjS.eulL_of_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:12.301341+00:00
-- url     : https://prove2.me/theorems/0003903a-12ee-4481-94b3-a482d9bc47ef
-- title:
--   Proj S: eul L of support
-- statement:
--   The Proj S construction uses the eul L of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L182-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L182-L188

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

theorem Formalism.GM.ProjS.eulL_of_support {s : ℕ} (t : Fin s → σ) (a : ℕ) (g : MvPolynomial σ k)
    (h : ∀ m ∈ g.support, ∑ c, m (t c) = a) : eulL t g = (a : k) • g := by sorry
