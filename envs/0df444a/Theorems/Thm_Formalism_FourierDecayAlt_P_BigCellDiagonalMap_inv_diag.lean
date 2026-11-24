-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_inv_diag
-- name    : Formalism.FourierDecayAlt.P.BigCellDiagonalMap.inv_diag
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:55:33.362429+00:00
-- url     : https://prove2.me/theorems/bb89c1ef-72b1-42a5-b756-080207ede4de
-- title:
--   Big Cell Diagonal Map: inv diag
-- statement:
--   The Big Cell Diagonal Map construction uses the inv diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDiagonalMap.lean#L84-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDiagonalMap.lean#L84-L90

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellDiagonalMap
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.BigCellDiagonalMap.inv_diag {r : ℕ} (v : Fin r → ℂ) (hv : ∀ a, v a ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun a => (v a)⁻¹) := by sorry
