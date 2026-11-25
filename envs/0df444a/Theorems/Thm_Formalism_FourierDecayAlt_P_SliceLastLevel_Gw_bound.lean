-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_Gw_bound
-- name    : Formalism.FourierDecayAlt.P.SliceLastLevel.Gw_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:06:10.534459+00:00
-- url     : https://prove2.me/theorems/e8df2d88-6b36-4897-b641-b67c7e4f8937
-- title:
--   Slice Last Level: Gw bound
-- statement:
--   The Slice Last Level construction uses the Gw bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L1984-L2028
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L1984-L2028

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
open scoped ContDiff
set_option linter.style.haveILetI false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r d : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.SliceLastLevel.Gw_bound {A : ℝ} {m : ℕ} (hT : TransportedAlt k r A m) {F : B.Mat k r → (Wq →L[ℂ] Wp)} {cF : ℝ}
    (hF : B.CCle A m F cF) {K : Set (Fin r → ℂ)} {C : ℝ} (hC : 1 ≤ C)
    (hs : ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1))
    {c : Fin r → ℂ} (hcK : c ∈ K) (hc : ∀ a, c a ≠ 0) {ξ : Mt k r × Mt k r} (hξ : ξ ∈ Sn k r)
    {μ : B.Mat k 0} (hμ : μ ∈ B.GV k 0) (w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)) (hw : w.length ≤ m) :
    ‖Gw F ξ w (phi k r c (Matrix.of ξ.1) (Matrix.of ξ.2) μ)‖ ≤
      beta0 (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) (Ap r A m) ξ := by sorry
