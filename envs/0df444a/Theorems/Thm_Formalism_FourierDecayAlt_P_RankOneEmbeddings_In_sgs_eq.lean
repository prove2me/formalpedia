-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_sgs_eq
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgs_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:43:42.942732+00:00
-- url     : https://prove2.me/theorems/3bbcf326-6109-430a-8176-24a86f4582b0
-- title:
--   In: sgs eq
-- statement:
--   The In construction uses the sgs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L924-L924
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L924-L924

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgs_eq (p : SS k r) (g : Mat k r) : sgs p g = sgF (p, g) := by sorry
