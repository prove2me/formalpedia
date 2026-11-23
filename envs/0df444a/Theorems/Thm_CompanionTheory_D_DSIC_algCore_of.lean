-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_algCore_of
-- name    : CompanionTheory.D.DSIC.algCore_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:56.810152+00:00
-- url     : https://prove2.me/theorems/84c1eddf-de8c-4570-ba71-b032a03c994d
-- title:
--   DSIC: alg Core of
-- statement:
--   The DSIC construction uses the alg Core of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L57-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CobApplyOfDeg.lean#L57-L99

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

theorem CompanionTheory.D.DSIC.algCore_of (hF : FRel) (hB : BdFacts) (hCO : CO) (hZ : ZetaHW) (hW : WLem) (hN : NormLt) (hA : Adj)
    (hP : PRV) : AlgCore := by sorry
