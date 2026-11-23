-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_K_antidiag_mul_diagonal
-- name    : Formalism.FourierDecayAlt.P.K.antidiag_mul_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:33.828273+00:00
-- url     : https://prove2.me/theorems/bc78264f-681e-436d-84ba-f6df153f933f
-- title:
--   K: antidiag mul diagonal
-- statement:
--   The K construction uses the antidiag mul diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L39-L51

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

theorem Formalism.FourierDecayAlt.P.K.antidiag_mul_diagonal (d : Fin n → K) :
    w0 n * diagonal d = Matrix.of fun i j => if i = Fin.rev j then d j else 0 := by sorry
