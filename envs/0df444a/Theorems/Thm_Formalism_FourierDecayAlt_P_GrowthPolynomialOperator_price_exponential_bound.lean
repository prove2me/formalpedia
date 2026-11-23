-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_price_exponential_bound
-- name    : Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.price_exponential_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:48.567245+00:00
-- url     : https://prove2.me/theorems/74cc600a-3e2a-4ef0-8aa7-070033c962e3
-- title:
--   Growth Polynomial Operator: price exponential bound
-- statement:
--   The Growth Polynomial Operator construction uses the price exponential bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L157-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L157-L198

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

theorem Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.price_exponential_bound (f k : ℕ) (b g : ℝ) (hb : 1 ≤ b) (hk : 1 ≤ k) (hf : f ≤ k)
    (hg : ((k : ℝ) * b) ^ 8 ≤ g) :
    0 < g ∧ (f : ℝ) / g ≤ (b ^ 7)⁻¹ ∧ 0 ≤ (1 + 3 / g) ^ f ∧
      (1 + 3 / g) ^ f ≤ Real.exp (3 * (b ^ 7)⁻¹) := by sorry
