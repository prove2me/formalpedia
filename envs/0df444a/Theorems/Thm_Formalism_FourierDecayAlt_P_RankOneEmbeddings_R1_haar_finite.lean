-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_finite
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:43:50.782063+00:00
-- url     : https://prove2.me/theorems/8c75607b-8807-4493-817e-badd690224f0
-- title:
--   R1: haar finite
-- statement:
--   The R1 construction uses the haar finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L618-L624
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L618-L624

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

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite (KW : CompactW) {z : Vc k r} (hz : inWb k r z) (hT : 0 < Tz k r z) {μW : Measure (Mt k r)}
    (hW : IsHaarOn (UWset k r z) μW) : IsFiniteMeasure μW := by sorry
