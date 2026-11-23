-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_euler_product_bounds
-- name    : Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.euler_product_bounds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:18.798244+00:00
-- url     : https://prove2.me/theorems/cb6ee1cb-1e97-44c0-9cb3-4d5fb9c9a39b
-- title:
--   Growth Polynomial Operator: euler product bounds
-- statement:
--   The Growth Polynomial Operator construction uses the euler product bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L14-L36

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
open Formalism.FourierDecayAlt.PB Finset

theorem Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.euler_product_bounds (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 1 / 3) (k : ℕ) :
    1 - 3 / 2 * x + 3 / 2 * x ^ (k + 1) ≤ ∏ i ∈ Icc 1 k, (1 - x ^ i) ∧
      ∏ i ∈ Icc 1 k, (1 - x ^ i) ≤ 1 := by sorry
