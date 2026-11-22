-- Prove2me | Theorems.Thm_Formalism_FN_gNorm_bdd_of_conv
-- name    : Formalism.FN.gNorm_bdd_of_conv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:40.866867+00:00
-- url     : https://prove2.me/theorems/d8159a4f-bd98-4ce7-aea8-84d3f8cf64d2
-- title:
--   FN: g Norm bdd of conv
-- statement:
--   The FN construction uses the g Norm bdd of conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NewtonSlope.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NewtonSlope.lean#L8-L9

import Definitions.Def_Formalism_SuccessiveMinima_StatementNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FN
open Filter Topology
variable {K : Type*} [NormedField K]

theorem Formalism.FN.gNorm_bdd_of_conv (a : ℕ → K) (r : ℝ) (h : ConvOn a r) :
    BddAbove (Set.range fun k : ℕ => ‖a k‖ * r ^ k) := by sorry
