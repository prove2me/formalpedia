-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_F_S_mul_k
-- name    : Formalism.GM.ProjS.F_S_mul_k
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:53.301835+00:00
-- url     : https://prove2.me/theorems/57fe9914-69e2-40b1-a84a-08593d85a758
-- title:
--   Proj S: F S mul k
-- statement:
--   The Proj S construction uses the F S mul k property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L329-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L329-L345

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

theorem Formalism.GM.ProjS.F_S_mul_k (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α β : k) (hW : eulL w g = α • g) (hE : eulL e g = β • g) :
    tieF w e ((∑ d, X (w d) * X (e d)) * g) =
      (∑ d, X (w d) * X (e d)) * tieF w e g + (α + β + s) • g := by sorry
