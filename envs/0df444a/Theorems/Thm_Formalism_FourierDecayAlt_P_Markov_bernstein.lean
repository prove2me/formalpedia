-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_bernstein
-- name    : Formalism.FourierDecayAlt.P.Markov.bernstein
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:25.459689+00:00
-- url     : https://prove2.me/theorems/92953389-b135-44d8-ab5c-8b308d9f12b2
-- title:
--   Markov: bernstein
-- statement:
--   The Markov construction uses the bernstein property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L205-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L205-L239

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset

theorem Formalism.FourierDecayAlt.P.Markov.bernstein (p : ℝ[X]) (n : ℕ) (hn : n ≠ 0) (hp : p.natDegree ≤ n) (M : ℝ)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) (θ : ℝ) :
    |sin θ * p.derivative.eval (cos θ)| ≤ n * M := by sorry
