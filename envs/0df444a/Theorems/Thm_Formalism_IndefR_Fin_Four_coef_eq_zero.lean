-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_coef_eq_zero
-- name    : Formalism.IndefR.Fin.Four.coef_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:08.651421+00:00
-- url     : https://prove2.me/theorems/03f15f6b-2b65-43e7-8417-02f8c702c213
-- title:
--   Four: coef eq zero
-- statement:
--   The Four construction uses the coef eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L146-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L146-L159

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y) (hχ0 : ∀ t y, χ t y ≠ 0)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X)))
include hfinX

theorem Formalism.IndefR.Fin.Four.coef_eq_zero (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) {a : W} (ha : a ∉ X) (y : W) :
    coef χ L X Φ a y = 0 := by sorry
