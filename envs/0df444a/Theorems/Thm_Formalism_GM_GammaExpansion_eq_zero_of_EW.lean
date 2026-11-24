-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_eq_zero_of_EW
-- name    : Formalism.GM.GammaExpansion.eq_zero_of_EW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:18.106812+00:00
-- url     : https://prove2.me/theorems/83eaf04e-afd5-400b-8605-0b2e596ecba3
-- title:
--   Gamma Expansion: eq zero of EW
-- statement:
--   The Gamma Expansion construction uses the eq zero of EW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L384-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L384-L396

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

theorem Formalism.GM.GammaExpansion.eq_zero_of_EW (a b : ℕ) (hab : a < b) (g : MvPolynomial σ k) (h : EW w g = ((a : k) - b) • g) :
    g = 0 := by sorry
