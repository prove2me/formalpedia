-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_fconj_eq
-- name    : Formalism.FourierDecayAlt.P.S3x5.fconj_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:17.398799+00:00
-- url     : https://prove2.me/theorems/689c8dba-a288-47b8-be81-99b97c2fe040
-- title:
--   S3x5: fconj eq
-- statement:
--   The S3x5 construction uses the fconj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L303-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L303-L306

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

theorem Formalism.FourierDecayAlt.P.S3x5.fconj_eq {q : ℕ} (hs : ∀ x : K, star x = x ^ q) {m n : Type} (X : Matrix m n K) :
    fconj q X = Xᴴ := by sorry
