-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_orbJ_cutF
-- name    : Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:44:26.263798+00:00
-- url     : https://prove2.me/theorems/7faea724-888d-4bbc-945f-8b8494c8ab85
-- title:
--   needs: orb J cut F
-- statement:
--   The needs construction uses the orb J cut F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L636-L668
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L636-L668

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

theorem Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF (Bs : RealPlaceData k r Wp Wq) (γ : Mat k r) (μR : Measure (Mt k r))
    (χ : ℝ → ℝ) (f : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ) :
    D.orbJ Bs γ μR (D.cutF Bs χ f ε) = ((χ (Gf k r Bs.z Bs.z' γ / ε) : ℝ) : ℂ) • D.orbJ Bs γ μR f := by sorry
