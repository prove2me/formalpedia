-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_herm_eq_zhat
-- name    : Formalism.FourierDecayAlt.P.Ux3.herm_eq_zhat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:26:04.557679+00:00
-- url     : https://prove2.me/theorems/1d1b1902-a8fc-4435-80e3-22aefb60f3f6
-- title:
--   Ux3: herm eq zhat
-- statement:
--   The Ux3 construction uses the herm eq zhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L382-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L382-L384

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

theorem Formalism.FourierDecayAlt.P.Ux3.herm_eq_zhat (r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v v = Zhat k r v v 1 (Fin.last r) (Fin.last r) := by sorry
