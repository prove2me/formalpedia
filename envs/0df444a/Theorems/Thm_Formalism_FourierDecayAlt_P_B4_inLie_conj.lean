-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_conj
-- name    : Formalism.FourierDecayAlt.P.B4.inLie_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:27:36.977305+00:00
-- url     : https://prove2.me/theorems/7b0467fc-466f-464b-9994-8b7c0b871498
-- title:
--   B4: in Lie conj
-- statement:
--   The B4 construction uses the in Lie conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L836-L864
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L836-L864

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.B4.inLie_conj {a X : Mat k r} (ha : a ∈ GV k r) (hX : inLie k r X) : inLie k r (a⁻¹ * X * a) := by sorry
