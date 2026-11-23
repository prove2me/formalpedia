-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_bound
-- name    : Formalism.FourierDecayAlt.P.WordLiftInduction.bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:48.058605+00:00
-- url     : https://prove2.me/theorems/8fc846be-5a5e-4533-9ca8-9aba837e83f2
-- title:
--   Word Lift Induction: bound
-- statement:
--   The Word Lift Induction construction uses the bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordLiftInduction.lean#L90-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordLiftInduction.lean#L90-L105

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordLiftInduction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem Formalism.FourierDecayAlt.P.WordLiftInduction.bound (Ξ : Sesq M) (d K : ℕ) (dat : Fin K → Dat R) (c : Fin K → ℂ)
    (grid : Fin K → Fin (d + 1) → ℝ) (X X' : M) (S : Fin K → ℝ) (B : ℝ)
    (hw : (∏ a, c a) * Ξ X X' =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1)
    (hS : ∀ a, ∑ i, |lagCo (grid a) i| = S a)
    (hB : ∀ j : Fin K → Fin (d + 1),
      ‖Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1‖ ≤ B) :
    (∏ a, ‖c a‖) * ‖Ξ X X'‖ ≤ (∏ a, S a) * B := by sorry
