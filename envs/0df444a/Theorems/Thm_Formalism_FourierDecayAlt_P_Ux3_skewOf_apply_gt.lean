-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_apply_gt
-- name    : Formalism.FourierDecayAlt.P.Ux3.skewOf_apply_gt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:53.669564+00:00
-- url     : https://prove2.me/theorems/f5e5c136-cba4-4ce0-b028-2469afc4bdcc
-- title:
--   Ux3: skew Of apply gt
-- statement:
--   The Ux3 construction uses the skew Of apply gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L600-L602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L600-L602

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

theorem Formalism.FourierDecayAlt.P.Ux3.skewOf_apply_gt {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) (a b : Fin n) (h : b < a) :
    skewOf q a b = -star (q.1 ⟨(b, a), h⟩) := by sorry
