-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_subdiagonal_sum_block2
-- name    : Formalism.FourierDecayAlt.P.Ux2.subdiagonal_sum_block2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:25:49.242954+00:00
-- url     : https://prove2.me/theorems/089fed5d-5d2c-4651-8c79-3c3eebad5ccc
-- title:
--   Ux2: subdiagonal sum block2
-- statement:
--   The Ux2 construction uses the subdiagonal sum block2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L700-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L700-L744

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
variable {p s : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux2.subdiagonal_sum_block2 (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    subS (blk2 A B C D) = subS A + (if h : 0 < s ∧ 0 < p then C ⟨0, h.1⟩ ⟨p - 1, by omega⟩ else 0) + subS D := by sorry
