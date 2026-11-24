-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_inv
-- name    : Formalism.FourierDecayAlt.P.C2x2.ut_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:48:54.702884+00:00
-- url     : https://prove2.me/theorems/edacc649-13e3-4266-9246-f275439fdfd9
-- title:
--   C2x2: ut inv
-- statement:
--   The C2x2 construction uses the ut inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L53-L55

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

theorem Formalism.FourierDecayAlt.P.C2x2.ut_inv {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u⁻¹ ∈ C2.UTset m := by sorry
