-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_cyclic_vectors_dense
-- name    : CompanionTheory.D.LK.cyclic_vectors_dense
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:25.417605+00:00
-- url     : https://prove2.me/theorems/5aae3902-26a6-4132-8ad1-9a6cc0f1ed0e
-- title:
--   LK: cyclic vectors dense
-- statement:
--   The LK construction uses the cyclic vectors dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CycDense.lean#L14-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CycDense.lean#L14-L52

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CycDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL (Cas)
open ReciprocityTheory.ChartRestriction.DS

theorem CompanionTheory.D.LK.cyclic_vectors_dense : CycDense := by sorry
