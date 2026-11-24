-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_avg
-- name    : Formalism.FourierDecayAlt.P.TwoByOneBlock.avg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:32:41.704635+00:00
-- url     : https://prove2.me/theorems/1c4a2503-e767-4293-a7ba-71895649b421
-- title:
--   Two By One Block: avg
-- statement:
--   The Two By One Block construction uses the avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1379-L1394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1379-L1394

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

theorem Formalism.FourierDecayAlt.P.TwoByOneBlock.avg {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW : Measure (Mt k r)} [SFinite μW]
    (hW : IsHaarOn (UWset k r z) μW) (T' : ℝ) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, ∫⁻ h, F (act h v) ∂μW ∂σV k r T' = μW Set.univ * ∫⁻ v, F v ∂σV k r T' := by sorry
