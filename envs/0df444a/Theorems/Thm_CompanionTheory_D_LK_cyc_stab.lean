-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_cyc_stab
-- name    : CompanionTheory.D.LK.cyc_stab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:50.197901+00:00
-- url     : https://prove2.me/theorems/5768aae0-6c4b-49e0-9987-a0cfc264b680
-- title:
--   LK: cyc stab
-- statement:
--   The LK construction uses the cyc stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/LowKMultOnePOf.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/LowKMultOnePOf.lean#L38-L43

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem CompanionTheory.D.LK.cyc_stab {E : Fin n → Fin n → Module.End ℂ V} {v w : V} (c d : Fin n) (h : w ∈ Cyc E v) :
    E c d w ∈ Cyc E v := by sorry
