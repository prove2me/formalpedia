-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_word_bound
-- name    : Formalism.FourierDecayAlt.P.SliceLastLevel.word_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:10.526348+00:00
-- url     : https://prove2.me/theorems/a74d04a2-87f1-4bef-b468-1d6c1379f72e
-- title:
--   Slice Last Level: word bound
-- statement:
--   The Slice Last Level construction uses the word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L1523-L1602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L1523-L1602

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
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.SliceLastLevel.word_bound {A : ℝ} {m : ℕ} (hT : TransportedAlt k r A m) {F : B.Mat k r → E} {cF : ℝ} (hF : B.CCle A m F cF)
    {C κ : ℝ} (hC : 1 ≤ C) (hκ : 1 ≤ κ) {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {μ : B.Mat k 0} (hμ : μ ∈ B.GV k 0)
    (hs1 : B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r))
    (hs2 : B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r))
    (hs3 : B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1))
    (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.inLie k r X ∧ ‖X‖ ≤ κ * B.gN n ^ 2)
    (hv : ∀ X ∈ v, B.inLie k r X ∧ ‖X‖ ≤ κ * B.gN n' ^ 2) (hl : u.length + v.length ≤ m) :
    ‖B.dLR u v F (phi k r c n n' μ)‖ ≤
      max cF 0 * (κ * C ^ 2) ^ m *
        (C ^ (3 * Ap r A m) * ((B.gN n * B.gN n') * B.gN μ) ^ (-Ap r A m)) := by sorry
