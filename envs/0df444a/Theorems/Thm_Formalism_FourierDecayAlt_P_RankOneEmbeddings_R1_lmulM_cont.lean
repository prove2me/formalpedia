-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_lmulM_cont
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.lmulM_cont
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:58:58.056521+00:00
-- url     : https://prove2.me/theorems/b12a5657-0665-48ce-a48a-7dce0b8cac76
-- title:
--   R1: lmul M cont
-- statement:
--   The R1 construction uses the lmul M cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L287-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L287-L290

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.lmulM_cont (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by sorry
