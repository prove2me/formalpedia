-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_local_bound
-- name    : Formalism.FourierDecayAlt.P.JFxG.local_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:26.378598+00:00
-- url     : https://prove2.me/theorems/96da9e23-9b17-4129-8671-c3365606077e
-- title:
--   JFx G: local bound
-- statement:
--   The JFx G construction uses the local bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L137-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L137-L165

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

theorem Formalism.FourierDecayAlt.P.JFxG.local_bound {F : Mat k r → E} (hF : CkOn ⊤ (GV k r) F) (m : ℕ) {g₀ : Mat k r} (hg₀ : g₀ ∈ GV k r) :
    ∃ V ∈ 𝓝 g₀, ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ V, x ∈ GV k r → ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool)
      (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F x‖ ≤ c := by sorry
