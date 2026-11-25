-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_unitLat_isLatIn
-- name    : Formalism.EigenvalueLevelCeiling.unitLat_isLatIn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:28:30.243933+00:00
-- url     : https://prove2.me/theorems/68ccd1da-1ffb-47ad-98ef-c93737e60001
-- title:
--   Eigenvalue Level Ceiling: unit Lat is Lat In
-- statement:
--   The Eigenvalue Level Ceiling construction uses the unit Lat is Lat In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L549-L559
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L549-L559

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem Formalism.EigenvalueLevelCeiling.unitLat_isLatIn : IsLatIn (⊤ : Submodule K K) (unitLat K) := by sorry
