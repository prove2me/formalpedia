-- Prove2me | Theorems.Thm_AlonMilman1985_thm2_7_multigraph_faithful
-- name    : AlonMilman1985.thm2_7_multigraph_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T00:25:33.908964+00:00
-- url     : https://prove2.me/theorems/a565e31d-cebf-4c2a-ab50-70310aa7fdee
-- title:
--   Theorem 2.7 for multigraphs, as used in the paper
-- statement:
--   Let $G$ be a loopless multigraph on a finite vertex set $V$ with $n = |V| > 1$, given by a symmetric multiplicity matrix $M \in \mathbb{N}^{V \times V}$ with zero diagonal ($M_{uv}$ is the number of edges between $u$ and $v$), and assume $G$ is connected. Let $d = \max_v \sum_w M_{vw}$ be its maximal degree and $\lambda_1$ the second-smallest eigenvalue, counted with multiplicity, of the Laplacian $Q = \operatorname{diag}\big(\sum_w M_{vw}\big) - M$. Then for all vertices $u, v$,
--
--   $$\operatorname{dist}_G(u,v) \le 2\Big\lfloor \sqrt{2d/\lambda_1}\,\log_2 n \Big\rfloor.$$
--
--   This is Theorem 2.7 of Alon and Milman (1985) in the generality the paper uses it, for graphs with parallel edges such as the Cayley graphs of Section 4 built on a multiset of generators. The existing theorem AlonMilman.Diameter.diameter_le_of_lambda1 is the special case of simple graphs ($M$ a 0/1 matrix).
--
--   **Formalization Note** Distance is measured in the underlying simple graph ($u \sim v$ iff $M_{uv} > 0$), which has the same distances as the multigraph. $\lambda_1$ is the eigenvalue at index $n-2$ of Mathlib's eigenvalue list of $Q$, which is sorted in decreasing order; the Hermitian hypothesis on $Q$ only names the proof needed to form that list and follows from the symmetry of $M$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), doi:10.1016/0095-8956(85)90092-9, p. 79, Theorem 2.7 (setup p. 76; multigraph uses pp. 80, 85–86)

import Mathlib

theorem AlonMilman1985.thm2_7_multigraph_faithful {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℕ) (hM : M.IsSymm) (hloop : ∀ v, M v v = 0)
    (hconn : (SimpleGraph.fromRel (fun u v => 0 < M u v)).Connected)
    (hn : 1 < Fintype.card V)
    (hQ : (Matrix.diagonal (fun v => ∑ w, (M v w : ℝ)) - M.map (fun m => (m : ℝ))).IsHermitian) :
    ∀ u v : V, (SimpleGraph.fromRel (fun u v => 0 < M u v)).dist u v ≤
      2 * ⌊Real.sqrt (2 * ((Finset.univ.sup (fun v => ∑ w, M v w) : ℕ) : ℝ) /
          hQ.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩) *
        Real.logb 2 (Fintype.card V : ℝ)⌋₊ := by sorry
