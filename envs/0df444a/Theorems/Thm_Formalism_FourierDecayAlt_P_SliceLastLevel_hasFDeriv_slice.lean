-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_hasFDeriv_slice
-- name    : Formalism.FourierDecayAlt.P.SliceLastLevel.hasFDeriv_slice
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:08:56.914901+00:00
-- url     : https://prove2.me/theorems/3555f325-a9f9-4e5b-a2c4-0c6c898a3106
-- title:
--   Slice Last Level: has FDeriv slice
-- statement:
--   The Slice Last Level construction uses the has FDeriv slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L1392-L1454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L1392-L1454

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
open Matrix Filter Topology
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r d : ℕ} {O : Set (Fin d → ℝ)} {cx : (Fin d → ℝ) → Fin r → ℂ} {μx : (Fin d → ℝ) → B.Mat k 0}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.SliceLastLevel.hasFDeriv_slice (hO : IsOpen O) (hcx : ContDiffOn ℝ ∞ cx O) (hμx : ContDiffOn ℝ ∞ μx O)
    (hx : ∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) {H : B.Mat k r → E}
    (hH : B.CkOn ((1 : ℕ) : ℕ∞) (B.GV k r) H) {n n' : B.Mat k r} (hn : n ∈ B.GV k r) (hn' : n' ∈ B.GV k r)
    {x : Fin d → ℝ} (hxO : x ∈ O) :
    HasFDerivAt (fun y => H (n⁻¹ * bmap k r cx μx y * n'))
      (∑ i, (aB k r cx μx i x).smulRight
        (Formalism.FourierDecayAlt.P.B4.op false (n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i * n') H (n⁻¹ * bmap k r cx μx x * n'))) x := by sorry
