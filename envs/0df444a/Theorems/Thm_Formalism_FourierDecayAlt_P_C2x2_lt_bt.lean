-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_lt_bt
-- name    : Formalism.FourierDecayAlt.P.C2x2.lt_bt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:58:49.138917+00:00
-- url     : https://prove2.me/theorems/0687990d-9f07-4412-ba88-e08ef16e5b4d
-- title:
--   C2x2: lt bt
-- statement:
--   The C2x2 construction uses the lt bt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L16-L17

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

theorem Formalism.FourierDecayAlt.P.C2x2.lt_bt {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l.BlockTriangular OrderDual.toDual := by sorry
