-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_add_smul_right
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_add_smul_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:09:25.61725+00:00
-- url     : https://prove2.me/theorems/a911251a-943d-58d7-a1e0-734e58b786b3
-- title:
--   Sign Antidiagonal: herm add smul right
-- statement:
--   The Sign Antidiagonal construction uses the herm add smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L26-L29

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
variable {k : ℕ}

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_add_smul_right {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w1 w2 : Fin n → ℂ) (a b : ℂ) :
    herm H v (a • w1 + b • w2) = star a * herm H v w1 + star b * herm H v w2 := by sorry
