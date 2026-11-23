-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_markov_nonneg
-- name    : Formalism.FourierDecayAlt.P.Markov.markov_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:39.644703+00:00
-- url     : https://prove2.me/theorems/8033da64-ffe4-4f64-9e8b-ffb8466c747f
-- title:
--   Markov: markov nonneg
-- statement:
--   The Markov construction uses the markov nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L241-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L241-L280

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

theorem Formalism.FourierDecayAlt.P.Markov.markov_nonneg (p : ℝ[X]) (n : ℕ) (hn : n ≠ 0) (hp : p.natDegree ≤ n) (M : ℝ)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 * M := by sorry
