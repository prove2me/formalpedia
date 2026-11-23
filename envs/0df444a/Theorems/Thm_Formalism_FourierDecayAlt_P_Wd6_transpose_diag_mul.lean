-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transpose_diag_mul
-- name    : Formalism.FourierDecayAlt.P.Wd6.transpose_diag_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:10.379798+00:00
-- url     : https://prove2.me/theorems/a20cfd9e-7798-4c16-a363-1bd4be4a1738
-- title:
--   Wd6: transpose diag mul
-- statement:
--   The Wd6 construction uses the transpose diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L110-L113

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

theorem Formalism.FourierDecayAlt.P.Wd6.transpose_diag_mul (M : M2 B) (z : B) :
    ((Matrix.diagonal fun _ => z) * M)ᵀ = (Matrix.diagonal fun _ => z) * Mᵀ := by sorry
