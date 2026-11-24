-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_skewOf_lt
-- name    : Formalism.FourierDecayAlt.P.Ux2.skewOf_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:47:20.105984+00:00
-- url     : https://prove2.me/theorems/5c1b2980-1d16-402b-8954-6059cf521b34
-- title:
--   Ux2: skew Of lt
-- statement:
--   The Ux2 construction uses the skew Of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L226-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L226-L227

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

theorem Formalism.FourierDecayAlt.P.Ux2.skewOf_lt (q : (G.UT j → ℂ) × (Fin j → ℝ)) {a b : Fin j} (h : a < b) : skewOf q a b = q.1 ⟨(a, b), h⟩ := by sorry
