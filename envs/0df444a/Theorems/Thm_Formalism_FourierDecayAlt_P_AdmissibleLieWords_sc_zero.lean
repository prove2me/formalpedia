-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_sc_zero
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.sc_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:07:32.416188+00:00
-- url     : https://prove2.me/theorems/8a2a75a5-7a04-4fda-988f-4c1c802b0213
-- title:
--   Admissible Lie Words: sc zero
-- statement:
--   The Admissible Lie Words construction uses the sc zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfUnitWords.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfUnitWords.lean#L17-L19

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

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.sc_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε / 4) : sc ε x = 0 := by sorry
