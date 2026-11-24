-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_mat_ext_col
-- name    : Formalism.FourierDecayAlt.P.FlagGramRestriction.mat_ext_col
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:12.614072+00:00
-- url     : https://prove2.me/theorems/5f6807bc-1804-4e9a-891c-8a5493c52b0f
-- title:
--   Flag Gram Restriction: mat ext col
-- statement:
--   The Flag Gram Restriction construction uses the mat ext col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L25-L27

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FlagGramRestriction.mat_ext_col {n : ℕ} {ι : Type*} (A B : Matrix (Fin n) ι ℂ) (h : ∀ j, (fun a => A a j) = fun a => B a j) :
    A = B := by sorry
