-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_factor_pos
-- name    : Formalism.FourierDecayAlt.P.S3x5.factor_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:55:20.608441+00:00
-- url     : https://prove2.me/theorems/90afea30-c1dc-4787-ad6d-f863b8a64365
-- title:
--   S3x5: factor pos
-- statement:
--   The S3x5 construction uses the factor pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L47-L51

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

theorem Formalism.FourierDecayAlt.P.S3x5.factor_pos (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (hi : 1 ≤ i) :
    0 < 1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) := by sorry
