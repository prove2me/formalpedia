-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_conjTranspose
-- name    : Formalism.FourierDecayAlt.P.Ux3.skewOf_conjTranspose
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:30.991461+00:00
-- url     : https://prove2.me/theorems/1b96ece2-6c57-4b90-a2ff-6025328fc7ed
-- title:
--   Ux3: skew Of conj Transpose
-- statement:
--   The Ux3 construction uses the skew Of conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L219-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L219-L228

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

theorem Formalism.FourierDecayAlt.P.Ux3.skewOf_conjTranspose {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) : (skewOf q)ᴴ = -skewOf q := by sorry
