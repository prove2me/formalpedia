-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_tiePhi_eq
-- name    : Formalism.GM.GammaExpansion.tiePhi_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:45.74183+00:00
-- url     : https://prove2.me/theorems/836b8783-213d-4d4a-832c-1ba3cc24bd31
-- title:
--   Gamma Expansion: tie Phi eq
-- statement:
--   The Gamma Expansion construction uses the tie Phi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L452-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L452-L456

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

theorem Formalism.GM.GammaExpansion.tiePhi_eq (o n z : ℕ) (u : MvPolynomial σ k) :
    tiePhi w e o n z u = ∑ j ∈ range (o + 1), cph k (o + n + r + z - 1) j • (tieE w e ^ j) ((tieF w e ^ j) u) := by sorry
