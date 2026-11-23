-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_K_right_eq_one
-- name    : Formalism.FourierDecayAlt.P.K.right_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:48.934826+00:00
-- url     : https://prove2.me/theorems/96456570-9dc6-46ee-9468-a3b161db7628
-- title:
--   K: right eq one
-- statement:
--   The K construction uses the right eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L91-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L91-L99

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

theorem Formalism.FourierDecayAlt.P.K.right_eq_one {b : Matrix (Fin n) (Fin n) K} {d : Fin n → K} (hd : ∀ x, d x ≠ 0)
    (h : (w0 n * diagonal d) * b = w0 n * diagonal d) : b = 1 := by sorry
