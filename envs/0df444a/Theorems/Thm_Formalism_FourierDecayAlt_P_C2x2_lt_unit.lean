-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_lt_unit
-- name    : Formalism.FourierDecayAlt.P.C2x2.lt_unit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:18:35.213798+00:00
-- url     : https://prove2.me/theorems/cc67f49a-64f6-4aa6-83ff-03474574b120
-- title:
--   C2x2: lt unit
-- statement:
--   The C2x2 construction uses the lt unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L50-L51

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

theorem Formalism.FourierDecayAlt.P.C2x2.lt_unit {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : IsUnit l.det := by sorry
