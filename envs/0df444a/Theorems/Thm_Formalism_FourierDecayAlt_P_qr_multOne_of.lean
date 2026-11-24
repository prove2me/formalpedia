-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_multOne_of
-- name    : Formalism.FourierDecayAlt.P.qr_multOne_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:12:21.478807+00:00
-- url     : https://prove2.me/theorems/887404b9-8fba-4e03-8c36-a2b6563fdfbd
-- title:
--   P: qr mult One of
-- statement:
--   The P construction uses the qr mult One of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L154-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L154-L196

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr DegreeMapArithmetic

theorem Formalism.FourierDecayAlt.P.qr_multOne_of (hS : Qr.ExistsSingMax) (hD : Qr.DualMinor) (hP : Qr.SpanSing) : Qr.MultOne := by sorry
