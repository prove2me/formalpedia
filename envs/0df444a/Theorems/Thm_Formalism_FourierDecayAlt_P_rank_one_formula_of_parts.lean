-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_rank_one_formula_of_parts
-- name    : Formalism.FourierDecayAlt.P.rank_one_formula_of_parts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:40:20.085932+00:00
-- url     : https://prove2.me/theorems/6cbc344b-a229-4fcd-987f-4c210f2db54b
-- title:
--   P: rank one formula of parts
-- statement:
--   The P construction uses the rank one formula of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L761-L802
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L761-L802

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

theorem Formalism.FourierDecayAlt.P.rank_one_formula_of_parts : Formalism.FourierDecayAlt.B2.AssembleRankOne := by sorry
