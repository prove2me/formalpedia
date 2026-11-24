-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_lt_inv
-- name    : Formalism.FourierDecayAlt.P.C2x2.lt_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:01.327555+00:00
-- url     : https://prove2.me/theorems/b779d6fe-eefe-4638-b25b-f02d30b1e967
-- title:
--   C2x2: lt inv
-- statement:
--   The C2x2 construction uses the lt inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L57-L59

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

theorem Formalism.FourierDecayAlt.P.C2x2.lt_inv {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l⁻¹ ∈ C2.LTset m := by sorry
