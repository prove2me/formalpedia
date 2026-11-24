-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_piK_sub
-- name    : Formalism.IndefR.Fin.Four.piK_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:44.092609+00:00
-- url     : https://prove2.me/theorems/90e8ab0c-c077-4717-806b-71850a7a912d
-- title:
--   Four: pi K sub
-- statement:
--   The Four construction uses the pi K sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L78-L82

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

theorem Formalism.IndefR.Fin.Four.piK_sub {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] (G H : V) :
    piK ρ L X Y k (G - H) = piK ρ L X Y k G - piK ρ L X Y k H := by sorry
