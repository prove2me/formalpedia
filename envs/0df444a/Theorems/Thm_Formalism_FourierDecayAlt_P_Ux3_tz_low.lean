-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_tz_low
-- name    : Formalism.FourierDecayAlt.P.Ux3.tz_low
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:27:21.106133+00:00
-- url     : https://prove2.me/theorems/70814657-2535-49c0-83c2-937b2d54113d
-- title:
--   Ux3: tz low
-- statement:
--   The Ux3 construction uses the tz low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L386-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L386-L394

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

theorem Formalism.FourierDecayAlt.P.Ux3.tz_low (v : Fin (2 * (j + ρ) + k + 1) → ℂ) (hv : inWb k (j + ρ) v) :
    Tz k (j + ρ) v = Tz k ρ (lowV k j ρ v) := by sorry
