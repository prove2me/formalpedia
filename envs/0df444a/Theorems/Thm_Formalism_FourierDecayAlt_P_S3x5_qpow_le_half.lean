-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_qpow_le_half
-- name    : Formalism.FourierDecayAlt.P.S3x5.qpow_le_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:48.418125+00:00
-- url     : https://prove2.me/theorems/3e25f83b-ec9b-44dd-8205-4b7fe97301b6
-- title:
--   S3x5: qpow le half
-- statement:
--   The S3x5 construction uses the qpow le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L25-L32

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

theorem Formalism.FourierDecayAlt.P.S3x5.qpow_le_half (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (hi : 1 ≤ i) : (q : ℝ) ^ (-i) ≤ 1 / 2 := by sorry
