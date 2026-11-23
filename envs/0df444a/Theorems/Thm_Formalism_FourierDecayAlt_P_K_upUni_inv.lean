-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_K_upUni_inv
-- name    : Formalism.FourierDecayAlt.P.K.upUni_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:56.616634+00:00
-- url     : https://prove2.me/theorems/886d888c-27de-475f-837c-ab5f80f98902
-- title:
--   K: up Uni inv
-- statement:
--   The K construction uses the up Uni inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L31-L37

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

theorem Formalism.FourierDecayAlt.P.K.upUni_inv {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : IsUpUni a⁻¹ := by sorry
