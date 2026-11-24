-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_truncated_exponential_nonneg
-- name    : Formalism.FourierDecayAlt.P.TBBx1.truncated_exponential_nonneg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:04.532086+00:00
-- url     : https://prove2.me/theorems/90d8a020-900e-47f4-96ba-45fcf62a53e8
-- title:
--   TBBx1: truncated exponential nonneg
-- statement:
--   The TBBx1 construction uses the truncated exponential nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L96-L100

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section

theorem Formalism.FourierDecayAlt.P.TBBx1.truncated_exponential_nonneg (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) : 0 ≤ Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff 3 x t := by sorry
