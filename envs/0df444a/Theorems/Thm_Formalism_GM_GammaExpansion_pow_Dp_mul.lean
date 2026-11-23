-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_mul
-- name    : Formalism.GM.GammaExpansion.pow_Dp_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:21.433915+00:00
-- url     : https://prove2.me/theorems/22e80877-ea9f-40c9-b25f-cd8ac4783b3b
-- title:
--   Gamma Expansion: pow Dp mul
-- statement:
--   The Gamma Expansion construction uses the pow Dp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L28-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L28-L48

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

theorem Formalism.GM.GammaExpansion.pow_Dp_mul (v : σ) (a b : MvPolynomial σ R) (m : ℕ) :
    (Dp v ^ m) (a * b) = ∑ i ∈ range (m + 1), m.choose i • ((Dp v ^ i) a * (Dp v ^ (m - i)) b) := by sorry
