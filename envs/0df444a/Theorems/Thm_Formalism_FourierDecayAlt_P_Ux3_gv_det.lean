-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_gv_det
-- name    : Formalism.FourierDecayAlt.P.Ux3.gv_det
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:58:43.147595+00:00
-- url     : https://prove2.me/theorems/a5593645-ddc5-42be-b524-21308a02e473
-- title:
--   Ux3: gv det
-- statement:
--   The Ux3 construction uses the gv det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L479-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L479-L487

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux3.gv_det {r : ℕ} {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) : IsUnit γ.det := by sorry
