-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_finite
-- name    : Formalism.IndefR.Fin.Four.Gk_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:43.649827+00:00
-- url     : https://prove2.me/theorems/cc9aff0e-0ef8-44cc-9ef1-ea3735d3b17d
-- title:
--   Four: Gk finite
-- statement:
--   The Four construction uses the Gk finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L87-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L87-L109

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

theorem Formalism.IndefR.Fin.Four.Gk_finite (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y))) (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
    {k : ℕ} (hk : 0 < k) : Finite (Gk L Y k) := by sorry
