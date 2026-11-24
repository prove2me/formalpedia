-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_admissible_word_mem_lie
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.admissible_word_mem_lie
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:00.741232+00:00
-- url     : https://prove2.me/theorems/077998e8-eee5-41d9-a4cd-bcb9dbfa24d0
-- title:
--   Admissible Lie Words: admissible word mem lie
-- statement:
--   The Admissible Lie Words construction uses the admissible word mem lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L16-L18

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

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.admissible_word_mem_lie {n : ℕ} {w : List (Bool × Mat k r)} (h : admitted n w) : ∀ x ∈ w, inLie k r x.2 := by sorry
