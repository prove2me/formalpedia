-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_vec_wsum
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.vec_wsum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:59:09.558081+00:00
-- url     : https://prove2.me/theorems/8c4ad906-d762-424a-9439-8e6f4c6b18e2
-- title:
--   Sign Antidiagonal: vec wsum
-- statement:
--   The Sign Antidiagonal construction uses the vec wsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourthExpansionIdentity.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourthExpansionIdentity.lean#L9-L23

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarInverseSimplification
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthExpansionIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.vec_wsum (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) (p : Fin (2 * r + k + 1)) :
    v p = ∑ w : Fin (k + 1), v (wI k r w) * (if p = wI k r w then 1 else 0) := by sorry
