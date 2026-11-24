-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_mul_antiW
-- name    : Formalism.FourierDecayAlt.P.c2x2_mul_antiW
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:36:42.667703+00:00
-- url     : https://prove2.me/theorems/97014575-a53b-41e0-9c0f-fd6ec2ebc1c3
-- title:
--   P: c2x2 mul anti W
-- statement:
--   The P construction uses the c2x2 mul anti W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L149-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L149-L157

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
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
open C2x2

theorem Formalism.FourierDecayAlt.P.c2x2_mul_antiW {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    (M * C2.antiW s) i j = M i j.rev := by sorry
