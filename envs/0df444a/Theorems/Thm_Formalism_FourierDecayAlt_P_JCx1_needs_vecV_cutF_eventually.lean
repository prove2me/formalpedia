-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_vecV_cutF_eventually
-- name    : Formalism.FourierDecayAlt.P.JCx1.needs.vecV_cutF_eventually
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:45:24.169276+00:00
-- url     : https://prove2.me/theorems/905fad98-e194-4fc0-9a07-873029ba31d4
-- title:
--   needs: vec V cut F eventually
-- statement:
--   The needs construction uses the vec V cut F eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L670-L682
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L670-L682

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.JCx1.needs.vecV_cutF_eventually (hGS : D.PtGSpec) (Bs : RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ)
    (m₀ : Mat k r) (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (f : Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), D.vecV Bs ν' m₀ (D.cutF Bs χ f ε) p = D.vecV Bs ν' m₀ f p := by sorry
