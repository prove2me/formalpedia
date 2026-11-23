-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_monomial
-- name    : Formalism.GM.GammaExpansion.pow_Dp_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:28.610799+00:00
-- url     : https://prove2.me/theorems/7541ed03-fceb-409c-b80f-0a2d1f5fdf8c
-- title:
--   Gamma Expansion: pow Dp monomial
-- statement:
--   The Gamma Expansion construction uses the pow Dp monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L50-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L50-L68

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

theorem Formalism.GM.GammaExpansion.pow_Dp_monomial (v : σ) (s : σ →₀ ℕ) (c : R) (k : ℕ) :
    (Dp v ^ k) (monomial s c) = monomial (s - Finsupp.single v k) (c * ((s v).descFactorial k : R)) := by sorry
