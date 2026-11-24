-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tieF_pow_X_pow_mul
-- name    : Formalism.GM.ProjS.tieF_pow_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:16.970682+00:00
-- url     : https://prove2.me/theorems/b5af86b6-d71a-4799-8538-7d94d79e62bd
-- title:
--   Proj S: tie F pow X pow mul
-- statement:
--   The Proj S construction uses the tie F pow X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L280-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L280-L286

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

theorem Formalism.GM.ProjS.tieF_pow_X_pow_mul {r : ℕ} (w e : Fin r → σ) (zv : σ) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (z : ℕ)
    (g : MvPolynomial σ k) (l : ℕ) : (tieF w e ^ l) (X zv ^ z * g) = X zv ^ z * (tieF w e ^ l) g := by sorry
