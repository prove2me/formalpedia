-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_piK_smul
-- name    : Formalism.IndefR.Fin.Four.piK_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:11.768208+00:00
-- url     : https://prove2.me/theorems/e18d12a3-88d9-4aff-927f-ced6199bae33
-- title:
--   Four: pi K smul
-- statement:
--   The Four construction uses the pi K smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L72-L76

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

theorem Formalism.IndefR.Fin.Four.piK_smul {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] (c : ℂ) (G : V) :
    piK ρ L X Y k (c • G) = c • piK ρ L X Y k G := by sorry
