-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mulVec_jV
-- name    : Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:26:09.455006+00:00
-- url     : https://prove2.me/theorems/5168762e-ed31-4b1b-8114-ae4aa3ad755b
-- title:
--   Two By One Block: emb mul Vec j V
-- statement:
--   The Two By One Block construction uses the emb mul Vec j V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L219-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L219-L231

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    embWb k r μ *ᵥ jV k r u = jV k r (μ *ᵥ u) := by sorry
