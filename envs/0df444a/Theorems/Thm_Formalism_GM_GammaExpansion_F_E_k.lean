-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_F_E_k
-- name    : Formalism.GM.GammaExpansion.F_E_k
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:56.609042+00:00
-- url     : https://prove2.me/theorems/56e1935b-0407-4582-860f-7e87fc53b81d
-- title:
--   Gamma Expansion: F E k
-- statement:
--   The Gamma Expansion construction uses the F E k property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L290-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L290-L314

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

theorem Formalism.GM.GammaExpansion.F_E_k (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (α β : k) (Y : MvPolynomial σ k) (hW : EW w Y = α • Y) (hE : EW e Y = β • Y) :
    tieF w e (tieE w e Y) = tieE w e (tieF w e Y) + (α + β + r) • Y := by sorry
