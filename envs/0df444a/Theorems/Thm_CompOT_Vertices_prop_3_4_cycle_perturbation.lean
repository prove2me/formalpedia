-- Prove2me | Theorems.Thm_CompOT_Vertices_prop_3_4_cycle_perturbation
-- name    : CompOT.Vertices.prop_3_4_cycle_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:24.414248+00:00
-- url     : https://prove2.me/theorems/80c1aa6c-0623-4433-9581-637e6f116a01
-- title:
--   Proof of Proposition 3.4, p. 407 — a cycle in G(P) yields a nonzero perturbation E with zero row and column sums, supported on S(P)
-- statement:
--   Let $P$ be an $n \times m$ real matrix and let $G(P)$ be its support graph on $V \cup V'$, in which $i$ is joined to $j'$ exactly when $P_{ij} > 0$. If $G(P)$ contains a cycle, then there is a matrix $E \in \mathbb R^{n\times m}$ with
--   $$E \ne 0,\qquad E\mathbb 1_m = 0_n,\qquad E^\top \mathbb 1_n = 0_m,\qquad E_{ij} \ne 0 \implies P_{ij} > 0 .$$
--
--   This is the combinatorial half of the proof that extremal couplings have acyclic support: a cycle in the support yields a direction along which $P$ can be moved in both senses without changing its marginals.
--
--   **Formalization Note** The book scales the entries to $\pm\varepsilon$; here the scale is left to the companion statement on feasibility. No assumption on $P$ is needed.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.4.1, proof of Proposition 3.4, p. 407 (construction of the perturbation matrix E)

import Mathlib
import Definitions.Def_CompOT_Vertices_Defs

namespace CompOT.Vertices

/-- Proof of Proposition 3.4, p. 407: if the support graph `G(P)` contains a cycle, then
there is a nonzero perturbation matrix `E` whose row sums and column sums all vanish and which is supported on the support of `P`. No hypothesis on `P` is needed. -/
theorem prop_3_4_cycle_perturbation {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ)
    (hcyc : ¬ (supportGraph P).IsAcyclic) :
    ∃ E : Matrix (Fin n) (Fin m) ℝ, E ≠ 0 ∧
      (∀ i, ∑ j, E i j = 0) ∧ (∀ j, ∑ i, E i j = 0) ∧
      (∀ i j, E i j ≠ 0 → 0 < P i j) := by sorry

end CompOT.Vertices
