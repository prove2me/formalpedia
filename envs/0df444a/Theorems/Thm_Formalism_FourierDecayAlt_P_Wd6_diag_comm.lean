-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_diag_comm
-- name    : Formalism.FourierDecayAlt.P.Wd6.diag_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:38.434274+00:00
-- url     : https://prove2.me/theorems/5b3b4110-6eac-4898-9237-f3f34d7cdd08
-- title:
--   Wd6: diag comm
-- statement:
--   The Wd6 construction uses the diag comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L92-L96

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

theorem Formalism.FourierDecayAlt.P.Wd6.diag_comm {z : B} {M : M2 B} (h : EC z M) :
    (Matrix.diagonal fun _ => z) * M = M * (Matrix.diagonal fun _ => z) := by sorry
