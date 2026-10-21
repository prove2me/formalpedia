-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_theorem_3_2
-- name    : FeasibleBasesHC.Structure.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:51.605223+00:00
-- url     : https://prove2.me/theorems/af4149bb-7e23-493d-a3fb-33cc7eae3096
-- title:
--   Theorem 3.2, p. 8 — feasible split bases are connected
-- statement:
--   Let $(B,L,U)$ be an ultimate feasible basis of $\mathcal{WH}_\beta(G)$, and let $B'$ be its basic arcs in the split graph $G'$. For every $0<\beta<1$ the graph of $B'$ is connected, spans all split vertices, and has one nonbreakeven cycle:
--
--   $$B'\text{ is a good augmented tree spanning }V(G').$$
--
--   This strengthens the general GNF basis theorem, which only gives a forest of augmented-tree components.
--
--   **Formalization Note** The §3.2 standing scope is ultimate bases, as stated on p. 6. Paper node $1$ is `0 : Fin n`; `[NeZero n]` ensures it exists. Goodness is structural for every $\beta\in(0,1)$.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, pp. 6–8, Theorem 3.2 and the §3.2 ultimate-basis standing scope

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

namespace FeasibleBasesHC.Structure

/-- Theorem 3.2 in the ultimate-basis scope fixed at the start of §3.2. -/
theorem theorem_3_2 {n : ℕ} [NeZero n] (G : Digraph n)
    (b : Basis n) (hb : b ∈ GamUlt G) :
    ∀ beta : ℝ, 0 < beta → beta < 1 → (Gp G beta).IsGoodAugTree (Bp b) := by sorry

end FeasibleBasesHC.Structure
