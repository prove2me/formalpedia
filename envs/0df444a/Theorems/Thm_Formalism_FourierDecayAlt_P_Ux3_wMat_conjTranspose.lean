-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_conjTranspose
-- name    : Formalism.FourierDecayAlt.P.Ux3.wMat_conjTranspose
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:59:29.992219+00:00
-- url     : https://prove2.me/theorems/f79ae786-a6db-480c-bdbf-9ea8b75ea6f4
-- title:
--   Ux3: w Mat conj Transpose
-- statement:
--   The Ux3 construction uses the w Mat conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L211-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L211-L217

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

theorem Formalism.FourierDecayAlt.P.Ux3.wMat_conjTranspose (n : ℕ) : (G.wMat n)ᴴ = G.wMat n := by sorry
