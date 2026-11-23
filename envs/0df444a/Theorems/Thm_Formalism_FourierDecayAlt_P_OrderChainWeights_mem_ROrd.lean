-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_mem_ROrd
-- name    : Formalism.FourierDecayAlt.P.OrderChainWeights.mem_ROrd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:46.186318+00:00
-- url     : https://prove2.me/theorems/0be7d599-6b4f-4ef8-8639-8c5fb8310ccc
-- title:
--   Order Chain Weights: mem ROrd
-- statement:
--   The Order Chain Weights construction uses the mem ROrd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L9-L13

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

theorem Formalism.FourierDecayAlt.P.OrderChainWeights.mem_ROrd {o : Type} [CommRing o] [IsLocalRing o] (p : o × o) :
    p ∈ ROrd o ↔ IsLocalRing.residue o p.1 = IsLocalRing.residue o p.2 := by sorry
