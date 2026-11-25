-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ViF_star
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.ViF_star
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:31:30.035507+00:00
-- url     : https://prove2.me/theorems/1e673cde-976b-5f93-a86a-f69e43228dab
-- title:
--   Sign Antidiagonal: Vi F star
-- statement:
--   The Sign Antidiagonal construction uses the Vi F star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L91-L97

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal
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
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.ViF_star (q : Fin (2 * (m + 1) + k + 1)) (hq : m + 1 + k < q.val) :
    ViF m i Vc q = if (NFOne.sg k (m + 1) q).val = i.val then 1 else 0 := by sorry
