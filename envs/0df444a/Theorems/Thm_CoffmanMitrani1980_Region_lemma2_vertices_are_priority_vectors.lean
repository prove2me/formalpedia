-- Prove2me | Theorems.Thm_CoffmanMitrani1980_Region_lemma2_vertices_are_priority_vectors
-- name    : CoffmanMitrani1980.Region.lemma2_vertices_are_priority_vectors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:16:34.110393+00:00
-- url     : https://prove2.me/theorems/a72404e5-9387-4128-8363-8d6ec7eee95a
-- title:
--   Lemma 2 — every vertex of H** is a preemptive priority vector
-- statement:
--   Fix the model parameters ($\lambda_i,\mu_i>0$, $\rho<1$). Let $H^{**}$ be the set of performance vectors satisfying the conservation law (1) and the $2^M-2$ inequalities (4) for the proper nonempty sets of classes. Then every vertex of $H^{**}$ coincides with one of the preemptive priority vectors:
--   $$W\ \text{a vertex of } H^{**}\ \Longrightarrow\ W=P(i_1,\dots,i_M)\ \text{for some priority order } i_1,\dots,i_M.$$
--
--   With Lemma 1 at the priority vectors, this identifies the vertices of $H^{**}$ and gives $H^{**}\subseteq H$.
--
--   **Formalization Note.** A vertex is an extreme point of $H^{**}$ (`Set.extremePoints ℝ`).
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), DOI 10.1287/opre.28.3.810, p. 817, Lemma 2

import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

namespace CoffmanMitrani1980.Region

/-- **Lemma 2** of Coffman and Mitrani, Operations Research 28 (1980), p. 817 (PDF 9): "Let H\*\* be
the set of performance vectors which satisfy the conservation law (1) and the 2^M − 2 inequalities (4),
where g runs through all the proper nonempty subsets of {1, 2, ···, M}. Then, every vertex of H\*\*
coincides with one of the preemptive priority vectors P(1, 2, ···, M), ···, P(M, M − 1, ···, 1)."

**Formalization Note.** "Vertex" is read as an extreme point (`Set.extremePoints ℝ`); for a
polyhedron this is the same as a basic solution, the view of the paper's proof. -/
theorem lemma2_vertices_are_priority_vectors {M : ℕ} (p : Params M) :
    ∀ W ∈ Set.extremePoints ℝ p.Hss, ∃ π : Equiv.Perm (Fin M), W = p.prioVec π := by sorry

end CoffmanMitrani1980.Region
