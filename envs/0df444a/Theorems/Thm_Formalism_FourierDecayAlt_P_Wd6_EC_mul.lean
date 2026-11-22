-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_EC_mul
-- name    : Formalism.FourierDecayAlt.P.Wd6.EC.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:51.83036+00:00
-- url     : https://prove2.me/theorems/beea8ab1-682f-406f-826b-866e757f36b5
-- title:
--   EC: mul
-- statement:
--   The EC construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L79-L82

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

theorem Formalism.FourierDecayAlt.P.Wd6.EC.mul {z : B} {M N : M2 B} (hM : EC z M) (hN : EC z N) : EC z (M * N) := by sorry
