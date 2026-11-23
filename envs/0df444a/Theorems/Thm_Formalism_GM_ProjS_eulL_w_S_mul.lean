-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eulL_w_S_mul
-- name    : Formalism.GM.ProjS.eulL_w_S_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:37.181938+00:00
-- url     : https://prove2.me/theorems/148a2a4e-aa42-45a1-b4b0-97282a1da6b3
-- title:
--   Proj S: eul L w S mul
-- statement:
--   The Proj S construction uses the eul L w S mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L299-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L299-L306

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
variable {s : ℕ} {w e : Fin s → σ}

theorem Formalism.GM.ProjS.eulL_w_S_mul (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α : k) (hW : eulL w g = α • g) :
    eulL w ((∑ d, X (w d) * X (e d)) * g) = (α + 1) • ((∑ d, X (w d) * X (e d)) * g) := by sorry
