-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ibp
-- name    : Formalism.FourierDecayAlt.P.B5.ibp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:01:15.264658+00:00
-- url     : https://prove2.me/theorems/5292e2fc-8323-4943-81fb-a3044533901a
-- title:
--   B5: ibp
-- statement:
--   The B5 construction uses the ibp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L695-L730
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L695-L730

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_ibp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.B5.ibp (D : RealPlaceData k r Wp Wq) {X : Mat k r} (hX : inLie k r X) {f1 f2 : Mat k r → (Wq →L[ℂ] Wp)}
    (h1 : CkOn 1 (GV k r) f1) (h2 : CkOn 1 (GV k r) f2)
    (i0 : Integrable (fun g : Mt k r => hsInner (f1 (Matrix.of g)) (f2 (Matrix.of g))) D.μG)
    (i1 : Integrable (fun g : Mt k r => hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g))) D.μG)
    (i2 : Integrable (fun g : Mt k r => hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g))) D.μG) :
    (∫ g : Mt k r, hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g)) ∂D.μG) =
      -∫ g : Mt k r, hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g)) ∂D.μG := by sorry
