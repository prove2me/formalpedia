-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_list_smul_sum
-- name    : Formalism.FourierDecayAlt.P.JFxB.list_smul_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:25:53.584427+00:00
-- url     : https://prove2.me/theorems/61e3701c-616a-4546-b617-a2a024065576
-- title:
--   JFx B: list smul sum
-- statement:
--   The JFx B construction uses the list smul sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L296-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L296-L301

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

theorem Formalism.FourierDecayAlt.P.JFxB.list_smul_sum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (a : ℂ) (l : List ι)
    (c : ι → ℂ) (φ : ι → V) :
    a • (l.map fun i => c i • φ i).sum = (l.map fun i => c i • (a • φ i)).sum := by sorry
