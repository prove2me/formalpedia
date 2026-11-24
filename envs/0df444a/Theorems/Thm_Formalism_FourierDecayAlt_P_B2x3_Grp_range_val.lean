-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Grp_range_val
-- name    : Formalism.FourierDecayAlt.P.B2x3.Grp.range_val
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:54:32.413262+00:00
-- url     : https://prove2.me/theorems/69a11057-6b04-4f2a-b701-0ba3cc3c7ae6
-- title:
--   Grp: range val
-- statement:
--   The Grp construction uses the range val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L208-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L208-L208

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
open Formalism.FourierDecayAlt.P.B2x3.Grp
variable {k r : ℕ} {U : Set (Mat k r)} {h : IsClosedSubgroup U}

theorem Formalism.FourierDecayAlt.P.B2x3.Grp.range_val : Set.range (val : Grp U h → Mat k r) = U := by sorry
