-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_term_add_left
-- name    : Formalism.IndefR.Fin.Four.term_add_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:11.147989+00:00
-- url     : https://prove2.me/theorems/e29940f7-486a-4425-8d70-fa53ccd07314
-- title:
--   Four: term add left
-- statement:
--   The Four construction uses the term add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L162-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L162-L178

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

theorem Formalism.IndefR.Fin.Four.term_add_left (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x)) (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀)
    (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) (a : W) {y : W} (hy : y ∈ Y) {l : W} (hl : l ∈ L ⊓ X) :
    term ρ χ L X f₀ Φ (a + l) y = term ρ χ L X f₀ Φ a y := by sorry
