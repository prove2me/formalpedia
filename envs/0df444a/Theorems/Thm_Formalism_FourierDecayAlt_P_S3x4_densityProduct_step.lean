-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_densityProduct_step
-- name    : Formalism.FourierDecayAlt.P.S3x4.densityProduct_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:05.876495+00:00
-- url     : https://prove2.me/theorems/db9161e8-ed3e-44b2-9d0e-f31c3f24485d
-- title:
--   S3x4: density Product step
-- statement:
--   The S3x4 construction uses the density Product step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L393-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L393-L397

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.S3x4.densityProduct_step (q : ℕ) (lo hi : ℤ) (h : lo ≤ hi) :
    densP 1 q lo hi = (1 - (q : ℝ) ^ (-lo)) * densP 1 q (lo + 1) hi := by sorry
