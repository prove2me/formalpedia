-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ub_clm
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_clm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:23.559441+00:00
-- url     : https://prove2.me/theorems/4255e64a-f8e9-476c-bfff-6d676b702833
-- title:
--   Admissible Lie Words: ub clm
-- statement:
--   The Admissible Lie Words construction uses the ub clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L91-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L91-L102

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

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (hSG : S ⊆ GV k r) (hl : LSS f S) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f S n C e γ) :
    UB (fun g => L (f g)) S n (‖L‖ * C) e γ := by sorry
