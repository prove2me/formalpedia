-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eulL_mul
-- name    : Formalism.GM.ProjS.eulL_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:42.077798+00:00
-- url     : https://prove2.me/theorems/79385204-7a0b-4208-b123-d4838a770220
-- title:
--   Proj S: eul L mul
-- statement:
--   The Proj S construction uses the eul L mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L205-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L205-L210

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

theorem Formalism.GM.ProjS.eulL_mul {s : ℕ} (t : Fin s → σ) (f g : MvPolynomial σ k) :
    eulL t (f * g) = eulL t f * g + f * eulL t g := by sorry
