-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_rset_of_blocks
-- name    : Formalism.FourierDecayAlt.P.Ux2.rset_of_blocks
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:13.340338+00:00
-- url     : https://prove2.me/theorems/c6a2d0db-bc25-4ac0-b953-2df9d3370a9d
-- title:
--   Ux2: rset of blocks
-- statement:
--   The Ux2 construction uses the rset of blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L184-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L184-L206

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux2.rset_of_blocks {g : B.Mat k (j + ρ)} (hG : g ∈ B.GV k (j + ρ)) (h11 : b11 g = 1) (h21 : b21 g = 0)
    (h31 : b31 g = 0) (h22 : b22 g = 1) (h32 : b32 g = 0) : g ∈ Rset k j ρ := by sorry
