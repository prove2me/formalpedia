-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_topOk
-- name    : Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.topOk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:56.576503+00:00
-- url     : https://prove2.me/theorems/3fdadc89-9c34-4080-8e32-e0dc4915f312
-- title:
--   Growth Polynomial Operator: top Ok
-- statement:
--   The Growth Polynomial Operator construction uses the top Ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L843-L859
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L843-L859

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
variable {E : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.topOk (hA : J.PSDAgree) (hTP : J.TopPullback) (hTU : J.TopUnitHeads) (hN0 : A5.BaseKernelOne)
    (h1 : A5.SingleBlockThetaProps) {S : J.LocSys E (TB.Pt E)} {Y : Finset (TB.Pt E)} {un : Bool}
    (h : IsTopSys S Y un) :
    ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels S S' Y ∧
      (un = true → ∀ t : E, t ≠ 0 → TB.PSDOn Y (fun h h' =>
        (if t ∈ S.L then (1 : ℂ) else 0) - S.N t t h h')) := by sorry
