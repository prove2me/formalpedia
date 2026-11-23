-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_measurable_chainWeight
-- name    : Formalism.FourierDecayAlt.P.OrderChainWeights.measurable_chainWeight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:43.672849+00:00
-- url     : https://prove2.me/theorems/f423c8d8-8cb0-4f33-8a33-4c6cc7e17fef
-- title:
--   Order Chain Weights: measurable chain Weight
-- statement:
--   The Order Chain Weights construction uses the measurable chain Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L31-L39

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderChainWeights
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3
open scoped ENNReal

theorem Formalism.FourierDecayAlt.P.OrderChainWeights.measurable_chainWeight {X : Type} [MeasurableSpace X] (nrm : X → ℝ≥0∞) (hn : Measurable nrm)
    (i : ℕ) : Measurable (chainWeight nrm i) := by sorry
