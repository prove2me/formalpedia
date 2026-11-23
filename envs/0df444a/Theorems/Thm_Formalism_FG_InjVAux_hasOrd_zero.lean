-- Prove2me | Theorems.Thm_Formalism_FG_InjVAux_hasOrd_zero
-- name    : Formalism.FG.InjVAux.hasOrd_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:13.822617+00:00
-- url     : https://prove2.me/theorems/1e105fa3-6d8c-4ea3-9d9a-aa57e3585723
-- title:
--   Inj VAux: has Ord zero
-- statement:
--   The Inj VAux construction uses the has Ord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L21-L21

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

theorem Formalism.FG.InjVAux.hasOrd_zero (n : ℕ) : HasOrd n (0 : MvPowerSeries τ R) := by sorry
