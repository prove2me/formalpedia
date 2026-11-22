-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_prodb_pos
-- name    : Formalism.FourierDecayAlt.P.Sz7.prodb_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:39.794986+00:00
-- url     : https://prove2.me/theorems/6f7dea36-4d81-4f31-b2ac-0105a2ddcef9
-- title:
--   Sz7: prodb pos
-- statement:
--   The Sz7 construction uses the prodb pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L99-L103

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

theorem Formalism.FourierDecayAlt.P.Sz7.prodb_pos (c : Cfg) (h : c.Ok) : 0 < c.prodb := by sorry
