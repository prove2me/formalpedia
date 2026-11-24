-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_inv_mul
-- name    : Formalism.FourierDecayAlt.P.Ux3.uni_inv_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:27:38.810085+00:00
-- url     : https://prove2.me/theorems/cdcc623f-b215-4662-8fbe-1a3257f5efa8
-- title:
--   Ux3: uni inv mul
-- statement:
--   The Ux3 construction uses the uni inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L453-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L453-L457

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

theorem Formalism.FourierDecayAlt.P.Ux3.uni_inv_mul (a : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (b : Matrix (Fin j) (Fin j) ℂ)
    (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) :
    blk3 1 (-a) (a * c - b) 0 1 (-c) 0 0 1 * blk3 1 a b 0 1 c 0 0 1 = 1 := by sorry
