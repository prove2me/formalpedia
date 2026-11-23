-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transpose_mul_diag
-- name    : Formalism.FourierDecayAlt.P.Wd6.transpose_mul_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:04.861809+00:00
-- url     : https://prove2.me/theorems/7909fb05-6708-4006-94e6-3ae547049a62
-- title:
--   Wd6: transpose mul diag
-- statement:
--   The Wd6 construction uses the transpose mul diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L105-L108

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {B : Type} [Ring B]

theorem Formalism.FourierDecayAlt.P.Wd6.transpose_mul_diag (M : M2 B) (z : B) :
    (M * (Matrix.diagonal fun _ => z))ᵀ = Mᵀ * (Matrix.diagonal fun _ => z) := by sorry
