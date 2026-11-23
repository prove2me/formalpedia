-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_bd_apply_of_deg
-- name    : CompanionTheory.D.DSIC.bd_apply_of_deg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:06.210183+00:00
-- url     : https://prove2.me/theorems/fa95ee27-5f02-476e-8eb3-9e5f5cddaa10
-- title:
--   DSIC: bd apply of deg
-- statement:
--   The DSIC construction uses the bd apply of deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L38-L44

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

theorem CompanionTheory.D.DSIC.bd_apply_of_deg (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} {x : Ch ε V} (hx : Deg j x)
    {A : Finset (NC ε)} (hA : A.card = j) : bd ε E x A = 0 := by sorry
