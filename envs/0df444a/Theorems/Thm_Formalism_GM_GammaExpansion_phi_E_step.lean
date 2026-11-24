-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_phi_E_step
-- name    : Formalism.GM.GammaExpansion.phi_E_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:45.899806+00:00
-- url     : https://prove2.me/theorems/f2f15de8-1fcc-4547-9241-30d218dfc9ac
-- title:
--   Gamma Expansion: phi E step
-- statement:
--   The Gamma Expansion construction uses the phi E step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L458-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L458-L489

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

theorem Formalism.GM.GammaExpansion.phi_E_step (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (o' n' z : ℕ) (Z : MvPolynomial σ k) (hW : EW w Z = (o' : k) • Z) (hE : EW e Z = (n' : k) • Z) :
    tiePhi w e (o' + 1) (n' + 1) z (tieE w e Z) =
      (((z : k) + 1) / ((o' + n' + r + z + 1 : ℕ) : k)) • tieE w e (tiePhi w e o' n' (z + 1) Z) := by sorry
