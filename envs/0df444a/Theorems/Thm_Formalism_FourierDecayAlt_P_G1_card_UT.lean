-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G1_card_UT
-- name    : Formalism.FourierDecayAlt.P.G1.card_UT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:53.866055+00:00
-- url     : https://prove2.me/theorems/e9cde610-3ebb-45be-aa0d-36bec8c687a7
-- title:
--   G1: card UT
-- statement:
--   The G1 construction uses the card UT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L131-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L131-L139

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G1
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G1.card_UT (n : ℕ) : Fintype.card (UT n) = ∑ i ∈ range n, i := by sorry
