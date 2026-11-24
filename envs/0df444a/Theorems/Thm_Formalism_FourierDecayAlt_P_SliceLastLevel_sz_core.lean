-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_core
-- name    : Formalism.FourierDecayAlt.P.SliceLastLevel.sz_core
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:31.666949+00:00
-- url     : https://prove2.me/theorems/d421f3d6-36d6-46c8-a0c0-9c60ddaa8ee7
-- title:
--   Slice Last Level: sz core
-- statement:
--   The Slice Last Level construction uses the sz core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L359-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L359-L579

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.Ux5

theorem Formalism.FourierDecayAlt.P.SliceLastLevel.sz_core (k s : ℕ) (c : Fin (s + 1) → ℂ) (hc : ∀ a, c a ≠ 0) (Q : ℝ) (hQ2 : 2 ≤ Q)
    (hQr : ((s + 1 : ℕ) : ℝ) ≤ Q) (hQk : ((k + 1 : ℕ) : ℝ) ≤ Q) (hQc : ∀ a, ‖c a‖ ≤ Q) (hQK : 2 * unitriangularFactorConstant c ≤ Q)
    (hQd : (s.factorial : ℝ) / ‖∏ a, c a‖ ≤ Q) {n p : B.Mat k (s + 1)} (hn : n ∈ Nset k (s + 1))
    (hp : p ∈ Nset k (s + 1)) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hG : 1 ≤ B.gN (n⁻¹ * bigCell k (s + 1) c μ * p)) :
    EB n (Q ^ 5 * B.gN (n⁻¹ * bigCell k (s + 1) c μ * p) ^ (2 * s + 2)) ∧
    EB p (Q ^ 5 * B.gN (n⁻¹ * bigCell k (s + 1) c μ * p) ^ (2 * s + 2)) ∧
    EB μ (Q ^ 5 * B.gN (n⁻¹ * bigCell k (s + 1) c μ * p) ^ (s + 2)) := by sorry
