-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Grp_val_mul
-- name    : Formalism.FourierDecayAlt.P.B2x3.Grp.val_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:42:36.359841+00:00
-- url     : https://prove2.me/theorems/ec8ab4e5-a41a-4cae-bf22-a72830030221
-- title:
--   Grp: val mul
-- statement:
--   The Grp construction uses the val mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L203-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L203-L203

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

theorem Formalism.FourierDecayAlt.P.B2x3.Grp.val_mul (a b : Grp U h) : (a * b).val = a.val * b.val := by sorry
