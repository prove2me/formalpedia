-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_leviElement_mul_mMap
-- name    : Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_mul_mMap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:56:02.131665+00:00
-- url     : https://prove2.me/theorems/f1f0befe-623e-48d7-ab46-67afe776c4e2
-- title:
--   Big Cell Diagonal Map: levi Element mul m Map
-- statement:
--   The Big Cell Diagonal Map construction uses the levi Element mul m Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDiagonalMap.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDiagonalMap.lean#L17-L26

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

theorem Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_mul_mMap (W Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) (hW : IsUnit W.det) :
    muP k j ρ W * mMap k j ρ Z γ = mMap k j ρ (Wᴴ⁻¹ * Z) γ := by sorry
