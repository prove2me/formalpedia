-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_small_f
-- name    : Formalism.FourierDecayAlt.P.Sz9.small_f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:26.120807+00:00
-- url     : https://prove2.me/theorems/e2c26aa9-3f16-4d6b-801d-83508eeb08fb
-- title:
--   Sz9: small f
-- statement:
--   The Sz9 construction uses the small f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L21-L28

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz9
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz9.small_f (f k : ℕ) (hfk : f ≤ k) (hk : 7 ≤ k) : (f : ℝ) * (8 / 2 ^ k) ≤ Real.log 2 := by sorry
