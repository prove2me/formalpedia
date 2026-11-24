-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_cph_step
-- name    : Formalism.GM.GammaExpansion.cph_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:19.653486+00:00
-- url     : https://prove2.me/theorems/b5f4967d-50fc-487d-b8a5-fec9b17557cf
-- title:
--   Gamma Expansion: cph step
-- statement:
--   The Gamma Expansion construction uses the cph step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L423-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L423-L445

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

theorem Formalism.GM.GammaExpansion.cph_step (B t o' n' z : ℕ) (hB : B = o' + n' + r + z) (ht : t ≤ o') :
    cph k (B + 1) t + cph k (B + 1) (t + 1) * (((t : k) + 1) * ((o' : k) + n' + r - t)) =
      ((z : k) + 1) / ((B + 1 : ℕ) : k) * cph k B t := by sorry
