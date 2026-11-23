-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_geom_le
-- name    : Formalism.FourierDecayAlt.P.S3x5.geom_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:15.708204+00:00
-- url     : https://prove2.me/theorems/de0e59d8-5c09-4517-80ac-300ad3fcd93d
-- title:
--   S3x5: geom le
-- statement:
--   The S3x5 construction uses the geom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L60-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L60-L83

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

theorem Formalism.FourierDecayAlt.P.S3x5.geom_le (q : ℕ) (hq : 2 ≤ q) (a b : ℤ) :
    ∑ i ∈ Finset.Icc a b, (q : ℝ) ^ (-i) ≤ 2 * (q : ℝ) ^ (-a) := by sorry
