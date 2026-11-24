-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_mul
-- name    : Formalism.FourierDecayAlt.P.C2x2.ut_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:01.286075+00:00
-- url     : https://prove2.me/theorems/8ee45ec8-781e-495d-9343-bd3690cdfb2c
-- title:
--   C2x2: ut mul
-- statement:
--   The C2x2 construction uses the ut mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L61-L64

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
open Formalism.FourierDecayAlt.P.C2x2
variable {m : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x2.ut_mul {u v : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (hv : v ∈ C2.UTset m) :
    u * v ∈ C2.UTset m := by sorry
