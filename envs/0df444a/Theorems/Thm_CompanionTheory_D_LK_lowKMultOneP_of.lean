-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_lowKMultOneP_of
-- name    : CompanionTheory.D.LK.lowKMultOneP_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:13.130004+00:00
-- url     : https://prove2.me/theorems/cf13a51f-c833-4de5-a8c1-1881afc3c61f
-- title:
--   LK: low KMult One P of
-- statement:
--   The LK construction uses the low KMult One P of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/LowKMultOnePOf.lean#L205-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/LowKMultOnePOf.lean#L205-L274

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight CasK Cas)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsDS rhoC)
open CompanionTheory.D.DSIC (KRel KUnit KStab LowSpan HWMap)
variable {n : ℕ}

theorem CompanionTheory.D.LK.lowKMultOneP_of (hM : MultAlg) (hE : KModExists) (hD : CycDense) (hO : OrthCyc) : LowKMultOneP := by sorry
