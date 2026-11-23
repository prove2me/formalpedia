-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_EW_Fpow
-- name    : Formalism.GM.GammaExpansion.EW_Fpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:46.392011+00:00
-- url     : https://prove2.me/theorems/4a8db83c-5186-4c6b-9582-1b09e2b19535
-- title:
--   Gamma Expansion: EW Fpow
-- statement:
--   The Gamma Expansion construction uses the EW Fpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L316-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L316-L324

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

theorem Formalism.GM.GammaExpansion.EW_Fpow (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d) (α : k) (g : MvPolynomial σ k)
    (h : EW w g = α • g) (j : ℕ) : EW w ((tieF w e ^ j) g) = (α - j) • (tieF w e ^ j) g := by sorry
