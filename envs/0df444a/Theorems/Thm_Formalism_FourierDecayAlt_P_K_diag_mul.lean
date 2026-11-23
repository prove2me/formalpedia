-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_K_diag_mul
-- name    : Formalism.FourierDecayAlt.P.K.diag_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:41.624121+00:00
-- url     : https://prove2.me/theorems/69bb82eb-2d91-46a5-8b83-a5d481fdfb41
-- title:
--   K: diag mul
-- statement:
--   The K construction uses the diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L10-L18

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.K
open Matrix Finset Real Formalism.FourierDecayAlt.K
variable {K : Type} [Field K] {n : ℕ}

theorem Formalism.FourierDecayAlt.P.K.diag_mul {a b : Matrix (Fin n) (Fin n) K} (ha : a.BlockTriangular id)
    (hb : b.BlockTriangular id) (i : Fin n) : (a * b) i i = a i i * b i i := by sorry
