-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_dsInfCharCap_of
-- name    : CompanionTheory.D.DSIC.dsInfCharCap_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:04.651639+00:00
-- url     : https://prove2.me/theorems/a38f4133-f288-48a8-9969-ff7c1a4b113a
-- title:
--   DSIC: ds Inf Char Cap of
-- statement:
--   The DSIC construction uses the ds Inf Char Cap of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L101-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L101-L122

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

theorem CompanionTheory.D.DSIC.dsInfCharCap_of (hC : AlgCoreSub) (hM : SmMod) (hQ : ActQ) (hSp : Spread) (hKS : KFinSm) (hKF : KFinStab)
    (hSL : StabLink) (hH : HWofType) (hT : TypeOfHW) : PI.DSInfCharCap.DSInfCharCap := by sorry
