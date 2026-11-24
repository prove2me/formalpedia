-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_phi_contDiffAt
-- name    : Formalism.FourierDecayAlt.P.JFxG.phi_contDiffAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:17:00.541342+00:00
-- url     : https://prove2.me/theorems/3c3f4726-2af9-4f45-8bca-fbe1b2a79bee
-- title:
--   JFx G: phi cont Diff At
-- statement:
--   The JFx G construction uses the phi cont Diff At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L64-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L64-L83

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

theorem Formalism.FourierDecayAlt.P.JFxG.phi_contDiffAt (F' : Mat k r → E) {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (q : (Fin j → Mat k r) × Mat k r), q.2 ∈ U → ContDiffAt ℝ ∞ (Phi F' j bs) q := by sorry
