-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_chainWeight_snoc
-- name    : Formalism.FourierDecayAlt.P.OrderChainWeights.chainWeight_snoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:22.516289+00:00
-- url     : https://prove2.me/theorems/2bb70a58-1672-4f3f-a020-68a3193a0ad2
-- title:
--   Order Chain Weights: chain Weight snoc
-- statement:
--   The Order Chain Weights construction uses the chain Weight snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L15-L29

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

theorem Formalism.FourierDecayAlt.P.OrderChainWeights.chainWeight_snoc {X : Type} (nrm : X → ℝ≥0∞) (i : ℕ) (h : Fin i → X) (c : X) :
    chainWeight nrm (i + 1) (Fin.snoc h c : Fin (i + 1) → X) =
      chainWeight nrm i h * (∏ l, nrm (h l)) ^ 2 := by sorry
