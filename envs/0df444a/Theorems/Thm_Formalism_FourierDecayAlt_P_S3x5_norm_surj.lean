-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_norm_surj
-- name    : Formalism.FourierDecayAlt.P.S3x5.norm_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:26.720123+00:00
-- url     : https://prove2.me/theorems/c7f1d602-eb6d-4362-ba19-e7cfcbfa7844
-- title:
--   S3x5: norm surj
-- statement:
--   The S3x5 construction uses the norm surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L352-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L352-L388

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
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]
variable [StarRing K]

theorem Formalism.FourierDecayAlt.P.S3x5.norm_surj {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2)
    (t : K) (ht : t ≠ 0) (hst : star t = t) : ∃ l : K, star l * l = t := by sorry
