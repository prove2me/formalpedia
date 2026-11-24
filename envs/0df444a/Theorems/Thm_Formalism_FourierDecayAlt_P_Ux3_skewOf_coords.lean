-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_coords
-- name    : Formalism.FourierDecayAlt.P.Ux3.skewOf_coords
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:27:16.809811+00:00
-- url     : https://prove2.me/theorems/ae5b1c2a-f2fe-4985-ba78-fdc79b56c608
-- title:
--   Ux3: skew Of coords
-- statement:
--   The Ux3 construction uses the skew Of coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L604-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L604-L622

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

theorem Formalism.FourierDecayAlt.P.Ux3.skewOf_coords {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : Sᴴ = -S) : skewOf (skewCoords S) = S := by sorry
