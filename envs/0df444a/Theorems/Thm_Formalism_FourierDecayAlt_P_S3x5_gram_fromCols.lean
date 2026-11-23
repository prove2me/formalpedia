-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_gram_fromCols
-- name    : Formalism.FourierDecayAlt.P.S3x5.gram_fromCols
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:18.730915+00:00
-- url     : https://prove2.me/theorems/d1dd2200-3a51-4d00-a15f-d2b6c9375d32
-- title:
--   S3x5: gram from Cols
-- statement:
--   The S3x5 construction uses the gram from Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L999-L1002
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L999-L1002

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
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]

theorem Formalism.FourierDecayAlt.P.S3x5.gram_fromCols {ν α β : Type} [Fintype ν] (J : Matrix ν ν K) (X : Matrix ν α K) (Y : Matrix ν β K) :
    (fromCols X Y)ᴴ * J * fromCols X Y =
      fromBlocks (Xᴴ * J * X) (Xᴴ * J * Y) (Yᴴ * J * X) (Yᴴ * J * Y) := by sorry
