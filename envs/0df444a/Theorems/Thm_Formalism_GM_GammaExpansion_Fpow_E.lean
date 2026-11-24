-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_Fpow_E
-- name    : Formalism.GM.GammaExpansion.Fpow_E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:48.458683+00:00
-- url     : https://prove2.me/theorems/fd9d936d-bf4f-43ce-8012-5d47f0d86bdd
-- title:
--   Gamma Expansion: Fpow E
-- statement:
--   The Gamma Expansion construction uses the Fpow E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L336-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L336-L350

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

theorem Formalism.GM.GammaExpansion.Fpow_E (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (α β : k) (Z : MvPolynomial σ k) (hW : EW w Z = α • Z) (hE : EW e Z = β • Z) (j : ℕ) :
    (tieF w e ^ (j + 1)) (tieE w e Z) =
      tieE w e ((tieF w e ^ (j + 1)) Z) + (((j : k) + 1) * (α + β + r - j)) • (tieF w e ^ j) Z := by sorry
