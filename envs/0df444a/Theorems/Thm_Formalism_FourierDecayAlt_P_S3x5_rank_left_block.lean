-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_rank_left_block
-- name    : Formalism.FourierDecayAlt.P.S3x5.rank_left_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:11.441241+00:00
-- url     : https://prove2.me/theorems/52aff326-c879-4319-8a2d-9f24cfba6e62
-- title:
--   S3x5: rank left block
-- statement:
--   The S3x5 construction uses the rank left block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L1005-L1030
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L1005-L1030

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

theorem Formalism.FourierDecayAlt.P.S3x5.rank_left_block {ν α β : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (J : Matrix ν ν K) (X : Matrix ν α K) (Y : Matrix ν β K)
    (S : Matrix (α ⊕ β) (α ⊕ β) K) (hS : IsUnit S.det)
    (h : (fromCols X Y)ᴴ * J * fromCols X Y = S) : X.rank = Fintype.card α := by sorry
