-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_model_mem_span
-- name    : Formalism.IndefR.Fin.Four.model_mem_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:14.034458+00:00
-- url     : https://prove2.me/theorems/62d353b8-3c9b-49cf-95a1-5397ba215432
-- title:
--   Four: model mem span
-- statement:
--   The Four construction uses the model mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L371-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L371-L393

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
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
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf
open Classical

theorem Formalism.IndefR.Fin.Four.model_mem_span (T : (W → ℂ) →ₗ[ℂ] V)
    (htr : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ))
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    {Φ : W → ℂ} (hΦ : IsSB L X Φ) :
    T Φ ∈ Submodule.span ℂ {v | ∃ a ∈ X, ∃ y ∈ Y, v = ρ a (ρ y f₀)} := by sorry
