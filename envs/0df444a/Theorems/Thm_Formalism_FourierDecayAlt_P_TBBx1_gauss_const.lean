-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_gauss_const
-- name    : Formalism.FourierDecayAlt.P.TBBx1.gauss_const
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:47.106341+00:00
-- url     : https://prove2.me/theorems/487e0892-c2ac-4545-97fb-34cd306ec288
-- title:
--   TBBx1: gauss const
-- statement:
--   The TBBx1 construction uses the gauss const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L150-L151

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

theorem Formalism.FourierDecayAlt.P.TBBx1.gauss_const : (4 * (3 / 2 : ℝ) ^ (3 : ℝ) * (3 / (3 - 2))) = 40.5 := by sorry
