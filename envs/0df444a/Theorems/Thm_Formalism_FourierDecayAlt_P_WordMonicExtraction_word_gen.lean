-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_word_gen
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.word_gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:37.937868+00:00
-- url     : https://prove2.me/theorems/e13bdc6d-7d90-416a-a5a8-8a30c5e4c416
-- title:
--   Word Monic Extraction: word gen
-- statement:
--   The Word Monic Extraction construction uses the word gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L277-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L277-L308

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.word_gen (Ξ : Sesq M) (d : ℕ) (X X' : M) : ∀ (K : ℕ) (dat : Fin K → Dat R)
    (grid : Fin K → Fin (d + 1) → ℝ) (c : Fin K → ℂ),
    (∀ a (Q Q' : R), ∑ i, ((lagCo (grid a) i : ℝ) : ℂ) *
      letterVal Ξ (dat a) (grid a i) (Q • X) (Q' • X') = c a * Ξ (Q • X) (Q' • X')) →
    ∀ Q Q' : R, (∏ a, c a) * Ξ (Q • X) (Q' • X') =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ (Q • X) (Q' • X') (List.ofFn fun a => (dat a, grid a (j a))) 1 1 := by sorry
