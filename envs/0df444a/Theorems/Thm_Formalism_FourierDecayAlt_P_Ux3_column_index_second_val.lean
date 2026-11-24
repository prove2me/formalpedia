-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_column_index_second_val
-- name    : Formalism.FourierDecayAlt.P.Ux3.column_index_second_val
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:59:27.67446+00:00
-- url     : https://prove2.me/theorems/8274b3c1-ea32-4450-b572-59cf2c6ce55f
-- title:
--   Ux3: column index second val
-- statement:
--   The Ux3 construction uses the column index second val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L290-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L290-L291

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

theorem Formalism.FourierDecayAlt.P.Ux3.column_index_second_val (c : Fin (ρ + 1)) : (eC j ρ (Sum.inr c)).val = j + c.val := by sorry
