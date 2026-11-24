-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_skewOf_ct
-- name    : Formalism.FourierDecayAlt.P.Ux2.skewOf_ct
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:50:07.909286+00:00
-- url     : https://prove2.me/theorems/b2a25d09-ae0d-4805-a1f5-946e6919dafa
-- title:
--   Ux2: skew Of ct
-- statement:
--   The Ux2 construction uses the skew Of ct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L220-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L220-L224

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

theorem Formalism.FourierDecayAlt.P.Ux2.skewOf_ct (q : (G.UT j → ℂ) × (Fin j → ℝ)) : (skewOf q)ᴴ = -skewOf q := by sorry
