-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_IsLev_mul
-- name    : Formalism.IndefR.Fin.Four.IsLev.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:29.412842+00:00
-- url     : https://prove2.me/theorems/f4e24e46-5c47-4988-a2e7-c7f9b59addbc
-- title:
--   Is Lev: mul
-- statement:
--   The Is Lev construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L41-L47

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_mul

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

theorem Formalism.IndefR.Fin.Four.IsLev.mul {ρ : W → Module.End ℂ V} {L X Y : AddSubgroup W} {k : ℕ} {G : V} (h : IsLev ρ L X Y k G) (j : ℕ) :
    IsLev ρ L X Y (k * j) G := by sorry
