-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_poly_adm
-- name    : Formalism.FourierDecayAlt.P.poly_adm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:54.423258+00:00
-- url     : https://prove2.me/theorems/5c64b956-bf23-484d-8ebd-08819cb50502
-- title:
--   P: poly adm
-- statement:
--   The P construction uses the poly adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfUnitWords.lean#L120-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfUnitWords.lean#L120-L130

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolynomialBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.poly_adm {k r d n : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) :
    ContDiff ℝ ∞ P ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → ∀ g ∈ GV k r, ‖Dw w P g‖ ≤ C * gN g ^ d := by sorry
