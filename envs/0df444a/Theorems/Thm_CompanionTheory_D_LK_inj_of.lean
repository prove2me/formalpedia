-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_inj_of
-- name    : CompanionTheory.D.LK.inj_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:42.262675+00:00
-- url     : https://prove2.me/theorems/36e36116-3323-495d-984e-13506e5427bd
-- title:
--   LK: inj of
-- statement:
--   The LK construction uses the inj of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/FilterAll.lean#L195-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/FilterAll.lean#L195-L314

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_FilterAll
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
open Car
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq lowK)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
variable {n : ℕ} {ε : Fin n → Bool}

theorem CompanionTheory.D.LK.inj_of (hV : VanK) (hP : WtProj) (hS : BdSq) : Inj := by sorry
