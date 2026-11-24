-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_embS_meas
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.embS_meas
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:58:18.15282+00:00
-- url     : https://prove2.me/theorems/ff79a411-a33a-42d5-9a30-60dc8f81eb0a
-- title:
--   R1: emb S meas
-- statement:
--   The R1 construction uses the emb S meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L405-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L405-L407

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

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.embS_meas {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) :
    Measurable fun ζ : ℂ => embF k r (s ζ) := by sorry
