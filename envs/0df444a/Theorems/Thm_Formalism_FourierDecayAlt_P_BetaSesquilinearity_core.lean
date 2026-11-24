-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_core
-- name    : Formalism.FourierDecayAlt.P.BetaSesquilinearity.core
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:52.956052+00:00
-- url     : https://prove2.me/theorems/f6f76762-990f-4309-bd82-01d61f07c461
-- title:
--   Beta Sesquilinearity: core
-- statement:
--   The Beta Sesquilinearity construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L1407-L1490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L1407-L1490

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {A : ℝ}

theorem Formalism.FourierDecayAlt.P.BetaSesquilinearity.core (hC : FormCoreC) (hAe : AeFromTests) (hFa : FatouParam) (hL : CCLin) (hDC : DilCC) (hA : 0 ≤ A)
    (hRB : RegBound D A) (hRA : RegAverage D A) (hU : Unfold D A) (hJ : JCont D A) (hDB : DilBeta D A)
    {τ₀ : ℝ × ℝ} (hτ₀ : τ₀ ∈ Quad) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (hF : InCC A 5 F) (hF' : InCC A 5 F') :
    betaTau D τ₀ F F' = betaInfTau D τ₀ F F' := by sorry
