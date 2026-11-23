-- Prove2me | Theorems.Thm_Formalism_FG_InjVAux_good_one
-- name    : Formalism.FG.InjVAux.good_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:01.566287+00:00
-- url     : https://prove2.me/theorems/fae63dbc-44a3-4a3f-80be-e7b27f1f4a26
-- title:
--   Inj VAux: good one
-- statement:
--   The Inj VAux construction uses the good one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L51-L52

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

theorem Formalism.FG.InjVAux.good_one (N : ℕ) : Good N 0 (1 : MvPowerSeries τ R) 1 := by sorry
