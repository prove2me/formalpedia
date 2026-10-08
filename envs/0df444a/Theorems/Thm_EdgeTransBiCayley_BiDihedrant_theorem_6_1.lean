-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiDihedrant_theorem_6_1
-- name    : EdgeTransBiCayley.BiDihedrant.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:39.746767+00:00
-- url     : https://prove2.me/theorems/d354e387-d7d8-4a26-9a42-bc1a958d583f
-- title:
--   Theorem 6.1 — a connected semisymmetric bi-dihedrant over D_n (n ≥ 3) has valency ≥ 6
-- statement:
--   Let $n \ge 3$ and let $\Gamma = \mathrm{BiCay}(H, R, L, S)$ be a connected semisymmetric bi-Cayley graph over the dihedral group $H = \langle a, b \mid a^n = b^2 = (ab)^2 = 1 \rangle \cong D_n$. Then every vertex $v$ of $\Gamma$ satisfies
--
--   $$
--   \deg_\Gamma(v) \ge 6.
--   $$
--
--   This is the lower half of Theorem 1.5: there is no semisymmetric bi-dihedrant of valency at most $5$.
--
--   **Formalization Note** $H$ is Mathlib's `DihedralGroup n` (order $2n$). The sets $R$, $L$, $S$ are arbitrary valid bi-Cayley data; the theorem is not restricted to $R = L = \emptyset$. Valency is the graph degree of each vertex.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 11, Theorem 6.1

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiDihedrant_Setting
open Pointwise

namespace EdgeTransBiCayley.BiDihedrant

theorem theorem_6_1 (n : ℕ) [NeZero n] (hn : 3 ≤ n) (D : BiCayData (DihedralGroup n))
    (hconn : D.graph.Connected) (hsemi : IsSemisymmetric D.graph) :
    ∀ v, 6 ≤ D.graph.degree v := by sorry

end EdgeTransBiCayley.BiDihedrant
