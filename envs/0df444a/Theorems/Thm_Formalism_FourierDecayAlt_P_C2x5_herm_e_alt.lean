-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_herm_e_alt
-- name    : Formalism.FourierDecayAlt.P.C2x5.herm_e_alt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:13:46.090166+00:00
-- url     : https://prove2.me/theorems/68d0537b-935b-40e9-b4c9-94c2866cba39
-- title:
--   C2x5: herm e alt
-- statement:
--   The C2x5 construction uses the herm e alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFlagVector.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFlagVector.lean#L37-L40

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

theorem Formalism.FourierDecayAlt.P.C2x5.herm_e_alt {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Fin (2 * r + k + 1))
    (hx : x.val < r ∨ r + k < x.val) : herm (Hpk k r) (bvec x) z = 0 := by sorry
