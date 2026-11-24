-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_coef_add_left
-- name    : Formalism.IndefR.Fin.Four.coef_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:15.985605+00:00
-- url     : https://prove2.me/theorems/bbeae754-5531-45a1-a3b0-47227d912af4
-- title:
--   Four: coef add left
-- statement:
--   The Four construction uses the coef add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L95-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L95-L134

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
include hχl hχ0 hfinX

theorem Formalism.IndefR.Fin.Four.coef_add_left (Φ : W → ℂ) (a y : W) {l : W} (hl : l ∈ L ⊓ X) :
    coef χ L X Φ (a + l) y = χ l y * coef χ L X Φ a y := by sorry
