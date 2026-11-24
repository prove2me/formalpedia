-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_middle_val
-- name    : Formalism.FourierDecayAlt.P.Ux3.block_index_middle_val
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:05:44.32544+00:00
-- url     : https://prove2.me/theorems/f47b8d7f-53ef-479c-9840-51f8d67e55a5
-- title:
--   Ux3: block index middle val
-- statement:
--   The Ux3 construction uses the block index middle val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L50-L51

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

theorem Formalism.FourierDecayAlt.P.Ux3.block_index_middle_val (i : Fin (2 * ρ + k + 1)) : (eB k j ρ (Sum.inl (Sum.inr i))).val = j + i.val := by sorry
