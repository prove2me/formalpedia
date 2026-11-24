-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_EW_add_single
-- name    : Formalism.GM.GammaExpansion.EW_add_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:54.802584+00:00
-- url     : https://prove2.me/theorems/40e26a3b-3d9f-46ec-8a3b-bc75bff186a7
-- title:
--   Gamma Expansion: EW add single
-- statement:
--   The Gamma Expansion construction uses the EW add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L243-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L243-L249

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

theorem Formalism.GM.GammaExpansion.EW_add_single (hwe : ∀ c d, w c ≠ e d) (c : Fin r) (g : MvPolynomial σ k) :
    EW w (pderiv (e c) g) = pderiv (e c) (EW w g) := by sorry
