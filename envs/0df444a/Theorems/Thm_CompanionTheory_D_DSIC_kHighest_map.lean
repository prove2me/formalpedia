-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_kHighest_map
-- name    : CompanionTheory.D.DSIC.kHighest_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:58.482768+00:00
-- url     : https://prove2.me/theorems/c7f6765d-bb85-4c61-9b20-4307c9fd6f77
-- title:
--   DSIC: k Highest map
-- statement:
--   The DSIC construction uses the k Highest map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L32-L36

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

theorem CompanionTheory.D.DSIC.kHighest_map {F : Fin n → Fin n → Module.End ℂ V} {γ : Fin n → ℝ} {x : V} (h : KHighest ε F γ x)
    {T : Module.End ℂ V} (hT : ∀ c d, ε c = ε d → Commute (F c d) T) : KHighest ε F γ (T x) := by sorry
