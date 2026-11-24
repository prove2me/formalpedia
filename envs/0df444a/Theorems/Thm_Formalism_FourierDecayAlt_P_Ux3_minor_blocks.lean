-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_minor_blocks
-- name    : Formalism.FourierDecayAlt.P.Ux3.minor_blocks
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:25:50.224842+00:00
-- url     : https://prove2.me/theorems/6b65ab7f-a005-4dfc-af93-d186bcb2b500
-- title:
--   Ux3: minor blocks
-- statement:
--   The Ux3 construction uses the minor blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L370-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L370-L380

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

theorem Formalism.FourierDecayAlt.P.Ux3.minor_blocks (Z : Matrix (Fin j) (Fin j) ℂ) (W : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ) (l : ℕ)
    (hl : l ≤ ρ + 1) (h : j + l ≤ j + ρ + 1) :
    ((Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Z 0 0 W)).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      Z.det * (W.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by sorry
