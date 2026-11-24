-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_EW_F
-- name    : Formalism.GM.GammaExpansion.EW_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:42.144615+00:00
-- url     : https://prove2.me/theorems/98d185d1-368d-45ba-ad4e-102166d364e6
-- title:
--   Gamma Expansion: EW F
-- statement:
--   The Gamma Expansion construction uses the EW F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L271-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L271-L275

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

theorem Formalism.GM.GammaExpansion.EW_F (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d) (α : k) (g : MvPolynomial σ k)
    (h : EW w g = α • g) : EW w (tieF w e g) = (α - 1) • tieF w e g := by sorry
