-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_unit_of_gram
-- name    : Formalism.FourierDecayAlt.P.S3x5.unit_of_gram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:22.582826+00:00
-- url     : https://prove2.me/theorems/638269e0-9058-43fa-9952-c88f3684d85c
-- title:
--   S3x5: unit of gram
-- statement:
--   The S3x5 construction uses the unit of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L714-L717
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L714-L717

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

theorem Formalism.FourierDecayAlt.P.S3x5.unit_of_gram {ν : Type} [Fintype ν] [DecidableEq ν] (J g : Matrix ν ν K) (hd : IsUnit J.det)
    (h : gᴴ * J * g = J) : IsUnit g.det := by sorry
