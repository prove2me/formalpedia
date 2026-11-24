-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ub_congr
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_congr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:33.313663+00:00
-- url     : https://prove2.me/theorems/260cbf48-9dd7-4d41-b7cb-a595f7778efb
-- title:
--   Admissible Lie Words: ub congr
-- statement:
--   The Admissible Lie Words construction uses the ub congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L50-L55

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_congr {f f₂ : Mat k r → E} {S : Set (Mat k r)} {V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V)
    (hSG : S ⊆ GV k r) (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f₂ S n C e γ) :
    UB f S n C e γ := by sorry
