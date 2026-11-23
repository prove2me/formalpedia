-- Prove2me | Theorems.Thm_Formalism_FG_InjVAux_hasOrd_zero_left
-- name    : Formalism.FG.InjVAux.hasOrd_zero_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:16.400851+00:00
-- url     : https://prove2.me/theorems/6a0b8383-b355-4605-8ab9-b9d9851b36aa
-- title:
--   Inj VAux: has Ord zero left
-- statement:
--   The Inj VAux construction uses the has Ord zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L18-L19

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open Formalism.FG.InjVAux
open MvPowerSeries
variable {R : Type*} [CommRing R] {τ : Type*}

theorem Formalism.FG.InjVAux.hasOrd_zero_left (z : MvPowerSeries τ R) : HasOrd 0 z := by sorry
