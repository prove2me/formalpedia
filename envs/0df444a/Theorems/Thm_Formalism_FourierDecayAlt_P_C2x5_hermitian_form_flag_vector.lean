-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_hermitian_form_flag_vector
-- name    : Formalism.FourierDecayAlt.P.C2x5.hermitian_form_flag_vector
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:12:55.520803+00:00
-- url     : https://prove2.me/theorems/2e7cf60d-f1c6-433a-bce9-a97e744ca4b8
-- title:
--   C2x5: hermitian form flag vector
-- statement:
--   The C2x5 construction uses the hermitian form flag vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFlagVector.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFlagVector.lean#L42-L49

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x5
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x5.hermitian_form_flag_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z c) z = if c.val = r then herm (Hpk k r) z z else 0 := by sorry
