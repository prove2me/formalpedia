-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_pointwise_stabiliser_of_explicit
-- name    : Formalism.FourierDecayAlt.P.OrderIndexAndStrata.pointwise_stabiliser_of_explicit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:49.941316+00:00
-- url     : https://prove2.me/theorems/137c9e1a-75ce-4c5d-b5a5-874c763863ec
-- title:
--   Order Index And Strata: pointwise stabiliser of explicit
-- statement:
--   The Order Index And Strata construction uses the pointwise stabiliser of explicit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L179-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L179-L243

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.OrderIndexAndStrata.pointwise_stabiliser_of_explicit (hS : SExplicit) : FrameStabiliserPointwise := by sorry
