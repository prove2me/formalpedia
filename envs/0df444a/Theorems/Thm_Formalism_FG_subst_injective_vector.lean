-- Prove2me | Theorems.Thm_Formalism_FG_subst_injective_vector
-- name    : Formalism.FG.subst_injective_vector
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:37.768772+00:00
-- url     : https://prove2.me/theorems/2405f129-06ab-434c-8f14-ef6f8e758fa9
-- title:
--   FG: subst injective vector
-- statement:
--   The FG construction uses the subst injective vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L155-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean#L155-L160

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
open MvPowerSeries

theorem Formalism.FG.subst_injective_vector : Formalism.FG.SubstInjectiveV.{u, v, w} := by sorry
