-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tieF_X_pow_mul
-- name    : Formalism.GM.ProjS.tieF_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:19.131209+00:00
-- url     : https://prove2.me/theorems/5330ae3e-2eaf-458d-9c42-ab8fadb8c5e9
-- title:
--   Proj S: tie F X pow mul
-- statement:
--   The Proj S construction uses the tie F X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L274-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L274-L278

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

theorem Formalism.GM.ProjS.tieF_X_pow_mul {r : ℕ} (w e : Fin r → σ) (zv : σ) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (z : ℕ)
    (g : MvPolynomial σ k) : tieF w e (X zv ^ z * g) = X zv ^ z * tieF w e g := by sorry
