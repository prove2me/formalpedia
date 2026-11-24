-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eq_zero_of_eulL
-- name    : Formalism.GM.ProjS.eq_zero_of_eulL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:02.540658+00:00
-- url     : https://prove2.me/theorems/c0d71d1e-2931-4d47-86f0-ecfeb5a504d6
-- title:
--   Proj S: eq zero of eul L
-- statement:
--   The Proj S construction uses the eq zero of eul L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L190-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L190-L203

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

theorem Formalism.GM.ProjS.eq_zero_of_eulL {s : ℕ} (t : Fin s → σ) (a b : ℕ) (hab : a < b) (g : MvPolynomial σ k) [CharZero k]
    (h : eulL t g = ((a : k) - (b : k)) • g) : g = 0 := by sorry
