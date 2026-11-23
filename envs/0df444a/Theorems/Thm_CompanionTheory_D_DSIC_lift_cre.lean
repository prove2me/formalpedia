-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_lift_cre
-- name    : CompanionTheory.D.DSIC.lift_cre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:05.943797+00:00
-- url     : https://prove2.me/theorems/7344456b-b907-4e80-93fd-9176ad898442
-- title:
--   DSIC: lift cre
-- statement:
--   The DSIC construction uses the lift cre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L24-L26

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CobApplyOfDeg
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
open CompanionTheory CompanionTheory.D CompanionTheory.D.DSIC
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsWtOn inG inK IsKStableOn)
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem CompanionTheory.D.DSIC.lift_cre (T : Module.End ℂ V) (i : NC ε) : Commute (lift ε T : Module.End ℂ (Ch ε V)) (cre i) := by sorry
