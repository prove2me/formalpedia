-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_surjective_of_rank
-- name    : Formalism.FourierDecayAlt.P.S3x4.surjective_of_rank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:15.23619+00:00
-- url     : https://prove2.me/theorems/bb68b356-69c0-434f-83a5-a44336420754
-- title:
--   S3x4: surjective of rank
-- statement:
--   The S3x4 construction uses the surjective of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L252-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L252-L258

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type} [Field K]

theorem Formalism.FourierDecayAlt.P.S3x4.surjective_of_rank {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a) :
    Function.Surjective (Matrix.toLin' Xᵀ) := by sorry
