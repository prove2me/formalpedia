-- Prove2me | Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
-- name    : Formalism.FG.InjVAux.HasOrd.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:32.157281+00:00
-- url     : https://prove2.me/theorems/0cc12608-4e6a-4d18-8906-6cf761485ebd
-- title:
--   Has Ord: add
-- statement:
--   The Has Ord construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L27-L29

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

theorem Formalism.FG.InjVAux.HasOrd.add {n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd n x) (hy : HasOrd n y) :
    HasOrd n (x + y) := by sorry
