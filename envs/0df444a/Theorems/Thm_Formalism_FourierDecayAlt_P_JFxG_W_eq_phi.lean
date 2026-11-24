-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_W_eq_phi
-- name    : Formalism.FourierDecayAlt.P.JFxG.W_eq_phi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:15:01.478806+00:00
-- url     : https://prove2.me/theorems/070c9f85-0513-4d29-ac68-11f7b1c40135
-- title:
--   JFx G: W eq phi
-- statement:
--   The JFx G construction uses the W eq phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L95-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L95-L109

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxG.W_eq_phi {F F' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U)
    (hff : ∀ x ∈ U, x ∈ GV k r → F x = F' x) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) →
      ∀ x ∈ U, x ∈ GV k r → W (List.ofFn fun i => (bs i, Xs i)) F x = Phi F' j bs (Xs, x) := by sorry
