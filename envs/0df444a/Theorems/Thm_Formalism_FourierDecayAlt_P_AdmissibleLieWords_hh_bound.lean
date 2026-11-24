-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_hh_bound
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.hh_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:07:23.986676+00:00
-- url     : https://prove2.me/theorems/2edc0390-7304-4b8a-8be8-11e2ab702688
-- title:
--   Admissible Lie Words: hh bound
-- statement:
--   The Admissible Lie Words construction uses the hh bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfUnitWords.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfUnitWords.lean#L50-L66

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.hh_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) {x : ℝ} (hx : ε ≤ x) :
    ‖iteratedFDeriv ℝ j (hh ε) x‖ ≤ |(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) := by sorry
