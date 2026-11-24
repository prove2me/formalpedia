-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_EW_pderiv_w
-- name    : Formalism.GM.GammaExpansion.EW_pderiv_w
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:51.48099+00:00
-- url     : https://prove2.me/theorems/903b5912-d32e-48fe-b7f5-5d5fae482bee
-- title:
--   Gamma Expansion: EW pderiv w
-- statement:
--   The Gamma Expansion construction uses the EW pderiv w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L251-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L251-L260

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

theorem Formalism.GM.GammaExpansion.EW_pderiv_w (hw : Function.Injective w) (c : Fin r) (g : MvPolynomial σ k) :
    EW w (pderiv (w c) g) = pderiv (w c) (EW w g) - pderiv (w c) g := by sorry
