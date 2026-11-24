-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eulL_tieF
-- name    : Formalism.GM.ProjS.eulL_tieF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:03.543253+00:00
-- url     : https://prove2.me/theorems/b30adeb7-d4f0-4f5f-9445-370994ba4b8d
-- title:
--   Proj S: eul L tie F
-- statement:
--   The Proj S construction uses the eul L tie F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L242-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L242-L248

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

theorem Formalism.GM.ProjS.eulL_tieF {s r : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (w e : Fin r → σ)
    (hmix : ∀ c, ((∃ d, t d = w c) ∧ ∀ d, t d ≠ e c) ∨ ((∀ d, t d ≠ w c) ∧ ∃ d, t d = e c))
    (g : MvPolynomial σ k) :
    eulL t (tieF w e g) = tieF w e (eulL t g) - tieF w e g := by sorry
