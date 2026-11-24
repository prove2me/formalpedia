-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_bt
-- name    : Formalism.FourierDecayAlt.P.C2x2.ut_bt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:15.200957+00:00
-- url     : https://prove2.me/theorems/810a6db5-a602-446d-af60-75c4a617547f
-- title:
--   C2x2: ut bt
-- statement:
--   The C2x2 construction uses the ut bt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L13-L14

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

theorem Formalism.FourierDecayAlt.P.C2x2.ut_bt {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.BlockTriangular id := by sorry
