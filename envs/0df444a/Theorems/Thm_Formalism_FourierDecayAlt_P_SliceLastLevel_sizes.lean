-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sizes
-- name    : Formalism.FourierDecayAlt.P.SliceLastLevel.sizes
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:07:06.186865+00:00
-- url     : https://prove2.me/theorems/bc3a3ab5-6485-4ba8-b6e1-30aa10efd627
-- title:
--   Slice Last Level: sizes
-- statement:
--   The Slice Last Level construction uses the sizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L643-L719
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L643-L719

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

theorem Formalism.FourierDecayAlt.P.SliceLastLevel.sizes (k r : ℕ) (K : Set (Fin r → ℂ)) (hK : IsCompact K) (hK0 : ∀ c ∈ K, ∀ a, c a ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1) := by sorry
