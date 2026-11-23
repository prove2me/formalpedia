-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_factor_bounds
-- name    : Formalism.FourierDecayAlt.P.S3x5.factor_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:40.166497+00:00
-- url     : https://prove2.me/theorems/3040d25f-a2ce-46b8-8515-533b754516eb
-- title:
--   S3x5: factor bounds
-- statement:
--   The S3x5 construction uses the factor bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L41-L45

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Finset Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.S3x5.factor_bounds (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (_hi : 1 ≤ i) :
    1 - (q : ℝ) ^ (-i) ≤ 1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) ∧
      1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) ≤ 1 + (q : ℝ) ^ (-i) := by sorry
