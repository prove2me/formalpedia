-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_tieE_pow_apply
-- name    : Formalism.GM.GammaExpansion.tieE_pow_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:30.284287+00:00
-- url     : https://prove2.me/theorems/9ebcd616-e486-45ac-832c-13d79e07aac0
-- title:
--   Gamma Expansion: tie E pow apply
-- statement:
--   The Gamma Expansion construction uses the tie E pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L398-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L398-L407

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}

theorem Formalism.GM.GammaExpansion.tieE_pow_apply (j : ℕ) (g : MvPolynomial σ k) :
    (tieE w e ^ j) g = (∑ c, X (w c) * X (e c)) ^ j * g := by sorry
