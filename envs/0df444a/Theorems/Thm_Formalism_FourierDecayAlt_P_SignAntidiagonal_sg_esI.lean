-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sg_esI
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.sg_esI
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:21.050702+00:00
-- url     : https://prove2.me/theorems/12774854-91c0-4fdd-8a1c-40677dab7346
-- title:
--   Sign Antidiagonal: sg es I
-- statement:
--   The Sign Antidiagonal construction uses the sg es I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OneAddProjectionMemIsotropicSet.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OneAddProjectionMemIsotropicSet.lean#L16-L20

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.sg_esI (b : Fin r) : NFOne.sg k r (esI k r b) = eI k r b := by sorry
