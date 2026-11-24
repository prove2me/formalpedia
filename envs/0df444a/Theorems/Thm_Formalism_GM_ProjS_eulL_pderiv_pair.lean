-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eulL_pderiv_pair
-- name    : Formalism.GM.ProjS.eulL_pderiv_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:01.433312+00:00
-- url     : https://prove2.me/theorems/b4c1b64b-5e68-45c6-abb3-daffa6716a4c
-- title:
--   Proj S: eul L pderiv pair
-- statement:
--   The Proj S construction uses the eul L pderiv pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L233-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L233-L240

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

theorem Formalism.GM.ProjS.eulL_pderiv_pair {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (a b : σ)
    (hab : ((∃ d, t d = a) ∧ ∀ d, t d ≠ b) ∨ ((∀ d, t d ≠ a) ∧ ∃ d, t d = b)) (g : MvPolynomial σ k) :
    eulL t (pderiv a (pderiv b g)) = pderiv a (pderiv b (eulL t g)) - pderiv a (pderiv b g) := by sorry
