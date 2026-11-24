-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_flatMap
-- name    : Formalism.FourierDecayAlt.P.JFxB.wsum_flatMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:42:30.918504+00:00
-- url     : https://prove2.me/theorems/908872b5-b271-4785-abd8-9547856ae3b8
-- title:
--   JFx B: wsum flat Map
-- statement:
--   The JFx B construction uses the wsum flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L42-L46

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxB.wsum_flatMap {ι : Type*} (l : List ι) (F : ι → List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (l.flatMap F) f g = (l.map fun i => wsum (F i) f g).sum := by sorry
