-- Prove2me | Theorems.Thm_Formalism_FG_InjVAux_Good_mul
-- name    : Formalism.FG.InjVAux.Good.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:15.543288+00:00
-- url     : https://prove2.me/theorems/9e146e76-7435-4324-a97c-718eb0d3f899
-- title:
--   Good: mul
-- statement:
--   The Good construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L54-L61

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

theorem Formalism.FG.InjVAux.Good.mul {N k l : ℕ} {x x' y y' : MvPowerSeries τ R} (hx : Good N k x x')
    (hy : Good N l y y') : Good N (k + l) (x * y) (x' * y') := by sorry
