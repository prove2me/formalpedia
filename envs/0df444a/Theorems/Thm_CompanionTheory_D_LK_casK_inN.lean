-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_casK_inN
-- name    : CompanionTheory.D.LK.casK_inN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:23.765045+00:00
-- url     : https://prove2.me/theorems/0c469aec-ce4f-49b6-8a52-23f30c58a7cf
-- title:
--   LK: cas K in N
-- statement:
--   The LK construction uses the cas K in N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/FilterAll.lean#L46-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/FilterAll.lean#L46-L67

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem CompanionTheory.D.LK.casK_inN {E : Fin n → Fin n → Module.End ℂ V} (hE : KRel ε E) (x : V) :
    InN ε E (CasK ε E x - (∑ c, E c c (E c c x) - ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • E c c x)) := by sorry
