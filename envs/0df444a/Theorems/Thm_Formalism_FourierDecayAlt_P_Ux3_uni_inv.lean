-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_inv
-- name    : Formalism.FourierDecayAlt.P.Ux3.uni_inv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:43.660663+00:00
-- url     : https://prove2.me/theorems/eb730487-8891-4117-9312-23d7892b4d68
-- title:
--   Ux3: uni inv
-- statement:
--   The Ux3 construction uses the uni inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L91-L93

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

theorem Formalism.FourierDecayAlt.P.Ux3.uni_inv (a : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (b : Matrix (Fin j) (Fin j) ℂ)
    (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) :
    (blk3 1 a b 0 1 c 0 0 1)⁻¹ = blk3 1 (-a) (a * c - b) 0 1 (-c) 0 0 1 := by sorry
