-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_gram_reindex
-- name    : Formalism.FourierDecayAlt.P.S3x5.gram_reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:24.602133+00:00
-- url     : https://prove2.me/theorems/195babfa-7e5f-48a0-bead-4b4ea2fd485e
-- title:
--   S3x5: gram reindex
-- statement:
--   The S3x5 construction uses the gram reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L708-L711
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L708-L711

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

theorem Formalism.FourierDecayAlt.P.S3x5.gram_reindex {ν ν' α α' : Type} [Fintype ν] [Fintype ν'] (e : ν' ≃ ν) (f : α' → α)
    (J : Matrix ν ν K) (Z : Matrix ν α K) :
    (Z.submatrix e f)ᴴ * J.submatrix e e * Z.submatrix e f = (Zᴴ * J * Z).submatrix f f := by sorry
