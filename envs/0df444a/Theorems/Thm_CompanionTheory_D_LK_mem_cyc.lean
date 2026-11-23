-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_mem_cyc
-- name    : CompanionTheory.D.LK.mem_cyc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:16.900034+00:00
-- url     : https://prove2.me/theorems/3192d0b7-88e6-4d2b-937b-5efa1e2c07f3
-- title:
--   LK: mem cyc
-- statement:
--   The LK construction uses the mem cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/LowKMultOnePOf.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/LowKMultOnePOf.lean#L33-L36

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

theorem CompanionTheory.D.LK.mem_cyc {E : Fin n → Fin n → Module.End ℂ V} {v w : V} : w ∈ Cyc E v ↔ ∃ a, ev E a v = w := by sorry
