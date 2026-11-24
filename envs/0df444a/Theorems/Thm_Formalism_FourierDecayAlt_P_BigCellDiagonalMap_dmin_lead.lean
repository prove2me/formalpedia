-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_dmin_lead
-- name    : Formalism.FourierDecayAlt.P.BigCellDiagonalMap.dmin_lead
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:55:49.701681+00:00
-- url     : https://prove2.me/theorems/280670ac-ad8d-4ae9-99f9-cfd400713fca
-- title:
--   Big Cell Diagonal Map: dmin lead
-- statement:
--   The Big Cell Diagonal Map construction uses the dmin lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDiagonalMap.lean#L124-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDiagonalMap.lean#L124-L133

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

theorem Formalism.FourierDecayAlt.P.BigCellDiagonalMap.dmin_lead {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (l : ℕ) (hl : l ≤ r) : Dmin k r z z' g ⟨l, by omega⟩ = Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl := by sorry
