-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_out
-- name    : Formalism.IndefR.Fin.Four.Gk_out
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:42.2306+00:00
-- url     : https://prove2.me/theorems/50ede3d9-8713-41be-98c3-71b4d3d46ac6
-- title:
--   Four: Gk out
-- statement:
--   The Four construction uses the Gk out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L75-L85

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

theorem Formalism.IndefR.Fin.Four.Gk_out {k : ℕ} (g : Gk L Y k) : (g : QY L Y).out ∈ Y ∧ k • (g : QY L Y).out ∈ L := by sorry
