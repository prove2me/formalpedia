-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_modul
-- name    : Formalism.IndefR.Fin.Four.IsSB.modul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:55.75437+00:00
-- url     : https://prove2.me/theorems/e1cbea74-58e4-4b50-95e3-273a2ecb658d
-- title:
--   Is SB: modul
-- statement:
--   The Is SB construction uses the modul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L63-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L63-L99

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
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
variable {L X : AddSubgroup W}

theorem Formalism.IndefR.Fin.Four.IsSB.modul {Y : AddSubgroup W} {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
    (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
    {Φ : W → ℂ} (h : IsSB L X Φ) {y : W} (hy : y ∈ Y) : IsSB L X (fun t => χ t y * Φ t) := by sorry
