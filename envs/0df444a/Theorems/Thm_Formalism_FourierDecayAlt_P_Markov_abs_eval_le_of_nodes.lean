-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_abs_eval_le_of_nodes
-- name    : Formalism.FourierDecayAlt.P.Markov.abs_eval_le_of_nodes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:37.728454+00:00
-- url     : https://prove2.me/theorems/1cd749ee-33e3-4fda-a7db-1d751b57b61e
-- title:
--   Markov: abs eval le of nodes
-- statement:
--   The Markov construction uses the abs eval le of nodes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L7-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L7-L51

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

theorem Formalism.FourierDecayAlt.P.Markov.abs_eval_le_of_nodes (s : Finset ℕ) (v : ℕ → ℝ) (hvs : Set.InjOn v s) (r : ℝ[X])
    (hr : r.degree < #s) (K : ℝ)
    (hK : ∀ i ∈ s, |r.eval (v i)| ≤ K * |(derivative (Lagrange.nodal s v)).eval (v i)|)
    (y : ℝ) (hy : ∀ i ∈ s, v i < y) :
    |r.eval y| ≤ K * (derivative (Lagrange.nodal s v)).eval y := by sorry
