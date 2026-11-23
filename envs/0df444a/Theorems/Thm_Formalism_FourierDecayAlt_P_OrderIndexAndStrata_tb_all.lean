-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_tb_all
-- name    : Formalism.FourierDecayAlt.P.OrderIndexAndStrata.tb_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:00.917796+00:00
-- url     : https://prove2.me/theorems/672f5dc0-a559-4af9-90d1-02ed8f5c6f74
-- title:
--   Order Index And Strata: tb all
-- statement:
--   The Order Index And Strata construction uses the tb all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L71-L75

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

theorem Formalism.FourierDecayAlt.P.OrderIndexAndStrata.tb_all : tb.Pos ∧ tb.InTwoA ∧ tb.InForm ∧ tb.InKernel ∧ tb.InMass ∧ tb.InDens ∧ tb.InTheoremA ∧
    tb.InJacMod ∧ tb.InNu ∧ tb.InInfinity ∧ tb.InVolumes ∧ tb.InLevelS ∧ tb.InMasses ∧ tb.InColumns ∧
    tb.InOrdinary ∧ tb.InTyped ∧ tb.InIndices := by sorry
