-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_tb_sharp
-- name    : Formalism.FourierDecayAlt.P.OrderIndexAndStrata.tb_sharp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:05.986489+00:00
-- url     : https://prove2.me/theorems/29d39443-fb15-4c15-9c4b-06f37822a9c2
-- title:
--   Order Index And Strata: tb sharp
-- statement:
--   The Order Index And Strata construction uses the tb sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L77-L79

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

theorem Formalism.FourierDecayAlt.P.OrderIndexAndStrata.tb_sharp : tb.GS = (1 + tb.δ) * tb.e1 * tb.tt * (tb.d * tb.d' / tb.Dstar) ∧ tb.Gam1 = 3 ∧
    tb.GS = 4/5 := by sorry
