-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dj_step
-- name    : Formalism.FourierDecayAlt.P.B2x8.dj_step
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:00:41.792055+00:00
-- url     : https://prove2.me/theorems/b941b0cf-9bfa-42d6-b38f-19a1732a181e
-- title:
--   B2x8: dj step
-- statement:
--   The B2x8 construction uses the dj step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1469-L1501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1469-L1501

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x8.dj_step (hU : HaarUnique) (hN : ClosedN) (hRec : NRecHaar) (hLev : DilLev) (hH : DilHeisMeas) (hK : KapRec)
    (k r' : ℕ) (μ' : Measure (Mt k r')) (hμ' : IsHaarOn (Nset k r') μ')
    (ih : ∀ t : ℝ, 0 < t → μ'.map (conjM (aDil k r' t)) = ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ')
    (μN : Measure (Mt k (1 + r'))) (hμN : IsHaarOn (Nset k (1 + r')) μN) (t : ℝ) (ht : 0 < t) :
    μN.map (conjM (aDil k (1 + r') t)) = ENNReal.ofReal ((t ^ kap k (1 + r'))⁻¹) • μN := by sorry
