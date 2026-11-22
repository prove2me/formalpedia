-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_split
-- name    : Formalism.FourierDecayAlt.P.S3x5.densityProduct_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:23.332854+00:00
-- url     : https://prove2.me/theorems/b5f60784-965a-4c9c-8d2b-9388b27494af
-- title:
--   S3x5: density Product split
-- statement:
--   The S3x5 construction uses the density Product split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L12-L23

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

theorem Formalism.FourierDecayAlt.P.S3x5.densityProduct_split (η : ℤ) (q : ℕ) (lo mid hi : ℤ) (h1 : lo ≤ mid + 1) (h2 : mid ≤ hi) :
    densP η q lo hi = densP η q lo mid * densP η q (mid + 1) hi := by sorry
