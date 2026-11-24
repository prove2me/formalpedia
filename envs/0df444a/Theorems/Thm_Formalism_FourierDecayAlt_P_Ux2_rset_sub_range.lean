-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_rset_sub_range
-- name    : Formalism.FourierDecayAlt.P.Ux2.rset_sub_range
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:23:06.955215+00:00
-- url     : https://prove2.me/theorems/99866318-6936-4840-b186-51094abe0eb6
-- title:
--   Ux2: rset sub range
-- statement:
--   The Ux2 construction uses the rset sub range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L266-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L266-L323

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

theorem Formalism.FourierDecayAlt.P.Ux2.rset_sub_range {g : B.Mat k (j + ρ)} (hg : g ∈ Rset k j ρ) : ∃ x, Rn k j ρ x = g := by sorry
