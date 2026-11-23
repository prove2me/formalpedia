-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_map_id_restrict
-- name    : Formalism.EigenvalueLevelCeiling.map_id_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:38:28.31654+00:00
-- url     : https://prove2.me/theorems/51e570b7-872e-4f99-bc01-8af545424240
-- title:
--   Eigenvalue Level Ceiling: map id restrict
-- statement:
--   The Eigenvalue Level Ceiling construction uses the map id restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L570-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L570-L574

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

theorem Formalism.EigenvalueLevelCeiling.map_id_restrict (A : Submodule (𝓞 K) K) :
    A.map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) = A := by sorry
