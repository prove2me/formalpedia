-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_mul_inv
-- name    : Formalism.FourierDecayAlt.P.Ux3.uni_mul_inv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:22:33.644553+00:00
-- url     : https://prove2.me/theorems/af07d442-e576-44cb-8c8b-d20c1d61abcf
-- title:
--   Ux3: uni mul inv
-- statement:
--   The Ux3 construction uses the uni mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L85-L89

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

theorem Formalism.FourierDecayAlt.P.Ux3.uni_mul_inv (a : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (b : Matrix (Fin j) (Fin j) ℂ)
    (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) :
    blk3 1 a b 0 1 c 0 0 1 * blk3 1 (-a) (a * c - b) 0 1 (-c) 0 0 1 = 1 := by sorry
