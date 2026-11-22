-- Prove2me | Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul
-- name    : Formalism.FG.InjVAux.HasOrd.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:21.077573+00:00
-- url     : https://prove2.me/theorems/172f62cc-b4b0-4706-805c-a860d627d26b
-- title:
--   Has Ord: mul
-- statement:
--   The Has Ord construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L35-L46

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

theorem Formalism.FG.InjVAux.HasOrd.mul {m n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd m x) (hy : HasOrd n y) :
    HasOrd (m + n) (x * y) := by sorry
