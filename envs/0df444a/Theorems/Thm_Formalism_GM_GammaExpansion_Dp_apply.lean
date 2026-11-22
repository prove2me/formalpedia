-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_Dp_apply
-- name    : Formalism.GM.GammaExpansion.Dp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:41.314804+00:00
-- url     : https://prove2.me/theorems/bad19348-689e-4893-8d66-9ff545714bde
-- title:
--   Gamma Expansion: Dp apply
-- statement:
--   The Gamma Expansion construction uses the Dp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L26-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L26-L26

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
variable {R σ : Type} [CommSemiring R]

theorem Formalism.GM.GammaExpansion.Dp_apply (v : σ) (p : MvPolynomial σ R) : Dp v p = pderiv v p := by sorry
