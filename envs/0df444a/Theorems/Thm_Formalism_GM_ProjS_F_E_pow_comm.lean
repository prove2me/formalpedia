-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_F_E_pow_comm
-- name    : Formalism.GM.ProjS.F_E_pow_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:53.60402+00:00
-- url     : https://prove2.me/theorems/2c613ac3-ee40-4d8c-a506-eb760f19f7f1
-- title:
--   Proj S: F E pow comm
-- statement:
--   The Proj S construction uses the F E pow comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L347-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L347-L368

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

theorem Formalism.GM.ProjS.F_E_pow_comm (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α β : k) (hW : eulL w g = α • g) (hE : eulL e g = β • g) (j : ℕ) :
    tieF w e ((tieE w e ^ (j + 1)) g) =
      (tieE w e ^ (j + 1)) (tieF w e g) + (((j : k) + 1) * (α + β + s + j)) • (tieE w e ^ j) g := by sorry
