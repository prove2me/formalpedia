-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_uwb_iff
-- name    : Formalism.FourierDecayAlt.P.B2x3.uwb_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:03:35.70041+00:00
-- url     : https://prove2.me/theorems/4ed14c3e-083e-4248-9547-cbf11b69db64
-- title:
--   B2x3: uwb iff
-- statement:
--   The B2x3 construction uses the uwb iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L588-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L588-L596

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x3.uwb_iff (g : Mat k r) : g ∈ UWb k r ↔ ∃ a, aᴴ * Hb k * a = Hb k ∧ embWb k r a = g := by sorry
