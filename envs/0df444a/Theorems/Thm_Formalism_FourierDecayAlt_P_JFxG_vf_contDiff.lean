-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_vf_contDiff
-- name    : Formalism.FourierDecayAlt.P.JFxG.vf_contDiff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:34:47.795625+00:00
-- url     : https://prove2.me/theorems/ddbcfca5-21ea-4a09-9cb3-2a5db5b716d6
-- title:
--   JFx G: vf cont Diff
-- statement:
--   The JFx G construction uses the vf cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L41-L51

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

theorem Formalism.FourierDecayAlt.P.JFxG.vf_contDiff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (b : Bool) {X g : P → Mat k r}
    (hX : ContDiff ℝ ∞ X) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun q => vf b (X q) (g q)) := by sorry
