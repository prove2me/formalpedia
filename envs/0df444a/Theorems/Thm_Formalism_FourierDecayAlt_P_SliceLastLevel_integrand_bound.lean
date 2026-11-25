-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_integrand_bound
-- name    : Formalism.FourierDecayAlt.P.SliceLastLevel.integrand_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:08:07.181827+00:00
-- url     : https://prove2.me/theorems/533a6f86-088d-4f02-a39c-ac7196cc615f
-- title:
--   Slice Last Level: integrand bound
-- statement:
--   The Slice Last Level construction uses the integrand bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L1699-L1750
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean#L1699-L1750

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.SliceLastLevel.integrand_bound {A : ℝ} {m : ℕ} (hT : TransportedAlt k r A m) {F : B.Mat k r → (Wq →L[ℂ] Wp)} {cF : ℝ}
    (hF : B.CCle A m F cF) {K : Set (Fin r → ℂ)} {C : ℝ} (hC : 1 ≤ C)
    (hs : ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1))
    {c : Fin r → ℂ} (hcK : c ∈ K) (hc : ∀ a, c a ≠ 0)
    (u v : List (B.Mat k 0)) (hu : ∀ X ∈ u, B.unitLie k 0 X) (hv : ∀ X ∈ v, B.unitLie k 0 X)
    (hl : u.length + v.length ≤ m) (μ : B.Mat k 0) (hμ : μ ∈ B.GV k 0) (ξ : Mt k r × Mt k r) :
    ‖B.dLR u v (hS F c ξ) μ‖ ≤
      (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) *
        (B.gN (Matrix.of ξ.1 : B.Mat k r) ^ (-Ap r A m) * B.gN (Matrix.of ξ.2 : B.Mat k r) ^ (-Ap r A m)) *
        B.gN μ ^ (-Ap r A m) := by sorry
