-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G1_prod_split
-- name    : Formalism.FourierDecayAlt.P.G1.prod_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:09.977221+00:00
-- url     : https://prove2.me/theorems/c8864697-1f06-40a5-9073-7e32a25c52cd
-- title:
--   G1: prod split
-- statement:
--   The G1 construction uses the prod split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L9-L12

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

theorem Formalism.FourierDecayAlt.P.G1.prod_split {n : ℕ} (x : Fin n → ℂ) (k : Fin n) :
    ∏ j, x j = x k * ∏ j ∈ univ \ {k}, x j := by sorry
