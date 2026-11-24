-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_measurable_inv_mulVec_embWb_of_measSec
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.measurable_inv_mulVec_embWb_of_measSec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:22:29.109575+00:00
-- url     : https://prove2.me/theorems/9d7bbe5b-67a1-4de5-ad31-85399e1f3064
-- title:
--   R1: measurable inv mul Vec emb Wb of meas Sec
-- statement:
--   The R1 construction uses the measurable inv mul Vec emb Wb of meas Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L505-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L505-L510

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

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.measurable_inv_mulVec_embWb_of_measSec {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (z' : Vc k r) :
    Measurable fun p : ℂ × Mt k r => (Matrix.of p.2 : Mat k r)⁻¹ *ᵥ (embWb k r (s p.1) *ᵥ z') := by sorry
