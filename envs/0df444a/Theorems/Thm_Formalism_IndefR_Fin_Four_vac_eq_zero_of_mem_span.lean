-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_vac_eq_zero_of_mem_span
-- name    : Formalism.IndefR.Fin.Four.vac_eq_zero_of_mem_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:57.392173+00:00
-- url     : https://prove2.me/theorems/f6d453b9-fa32-4b3d-9251-3f82b17ae08a
-- title:
--   Four: vac eq zero of mem span
-- statement:
--   The Four construction uses the vac eq zero of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L260-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L260-L299

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
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
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hY hXY hχl hχr hχ0 hLL hdY hfinX hfinY htf

theorem Formalism.IndefR.Fin.Four.vac_eq_zero_of_mem_span (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L) (Θ : Set V)
    (hlev : ∀ G ∈ Θ, ∃ k : ℕ, 0 < k ∧ IsLev ρ L X Y k G) {w : V}
    (hwX : ∀ u ∈ L ⊓ X, ρ u w = w) (hwY : ∀ u ∈ L ⊓ Y, ρ u w = w)
    (hw : w ∈ Submodule.span ℂ {v | ∃ u ∈ Y, ∃ G ∈ Θ, v = ρ u G - G}) : w = 0 := by sorry
