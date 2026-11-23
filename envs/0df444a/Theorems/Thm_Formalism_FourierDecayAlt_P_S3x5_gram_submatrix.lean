-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_gram_submatrix
-- name    : Formalism.FourierDecayAlt.P.S3x5.gram_submatrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:31.636256+00:00
-- url     : https://prove2.me/theorems/f888419a-a483-430c-bb6e-143a9f61da56
-- title:
--   S3x5: gram submatrix
-- statement:
--   The S3x5 construction uses the gram submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L480-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L480-L483

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
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]

theorem Formalism.FourierDecayAlt.P.S3x5.gram_submatrix {ν α β : Type} [Fintype ν] (J : Matrix ν ν K) (Z : Matrix ν α K) (e : β → α) :
    (Z.submatrix id e)ᴴ * J * (Z.submatrix id e) = (Zᴴ * J * Z).submatrix e e := by sorry
