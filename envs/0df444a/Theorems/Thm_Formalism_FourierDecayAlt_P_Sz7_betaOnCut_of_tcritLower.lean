-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_betaOnCut_of_tcritLower
-- name    : Formalism.FourierDecayAlt.P.Sz7.betaOnCut_of_tcritLower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:30.382803+00:00
-- url     : https://prove2.me/theorems/608d78c9-7370-4ce9-87df-ab43ed8f2a54
-- title:
--   Sz7: beta On Cut of tcrit Lower
-- statement:
--   The Sz7 construction uses the beta On Cut of tcrit Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L163-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L163-L254

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz7.betaOnCut_of_tcritLower (HT : TcritLower) : BetaOnCut := by sorry
