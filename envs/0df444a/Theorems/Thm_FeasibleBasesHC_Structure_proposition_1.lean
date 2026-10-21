-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_proposition_1
-- name    : FeasibleBasesHC.Structure.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:53.300991+00:00
-- url     : https://prove2.me/theorems/72a22687-43f5-4e1d-8e5e-370dd45a2f81
-- title:
--   Proposition 1, p. 6 — eventual stability of feasible bases
-- statement:
--   For a loopless digraph $G$ on $[n]$, the set $\Gamma(G,\beta)$ of feasible bases is constant once $\beta$ is sufficiently close to one. More precisely, there is $\alpha^*\in(0,1)$ such that
--
--   $$\Gamma(G,\beta)=\Gamma(G,\alpha^*)\qquad(\alpha^*\le\beta<1).$$
--
--   This identifies the eventual-basis set $\Gamma(G)$ with the stabilized feasible-basis set.
--
--   **Formalization Note** Paper node $1$ is `0 : Fin n`; `[NeZero n]` ensures it exists. The paper relates $\alpha^*$ to an earlier threshold $\alpha$; the statement quantifies one threshold satisfying the resulting stabilization claim.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 6, Proposition 1

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

namespace FeasibleBasesHC.Structure

/-- Proposition 1: the feasible-basis set stabilizes below one. -/
theorem proposition_1 {n : ℕ} [NeZero n] (G : Digraph n) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧
      ∀ beta : ℝ, alpha ≤ beta → beta < 1 → Gam G beta = Gam G alpha := by sorry

end FeasibleBasesHC.Structure
