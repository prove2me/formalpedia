-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiDihedrant_theorem_1_5
-- name    : EdgeTransBiCayley.BiDihedrant.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:37.224501+00:00
-- url     : https://prove2.me/theorems/cceb5f30-550b-446e-8c19-2ff610735f35
-- title:
--   Theorem 1.5 — connected semisymmetric bi-dihedrants have valency ≥ 6, and exist in valency 2k for each odd k ≥ 3
-- statement:
--   1. Let $n \ge 3$. Every connected semisymmetric bi-Cayley graph $\Gamma = \mathrm{BiCay}(D_n, R, L, S)$ over the dihedral group $D_n$ has valency at least $6$: $\deg_\Gamma(v) \ge 6$ for every vertex $v$.
--   2. For each odd integer $k \ge 3$ there exist $n \ge 3$ and a connected semisymmetric bi-Cayley graph over $D_n$ in which every vertex has degree
--
--   $$
--   \deg_\Gamma(v) = 2k.
--   $$
--
--   These are the first two sentences of Theorem 1.5. The lower bound shows that the smallest valency of a semisymmetric bi-dihedrant is $6$, and the examples show that every even valency $2k$ with $k \ge 3$ odd occurs.
--
--   **Formalization Note** "Bi-dihedrant" means a bi-Cayley graph over Mathlib's `DihedralGroup n`. The restriction $n \ge 3$ is that of Theorem 6.1 and §6 (for $n = 1, 2$ the group $D_n$ is abelian and is covered by the paper's results on bi-abelian graphs, not by this theorem's proof); it is disclosed here as a hypothesis of the first clause and a property of the witness in the second. Connectedness is included in the existence clause, as Example 6.2 provides. The third sentence of Theorem 1.5 (an edge-regular family of valency 6) rests on Theorem 6.5 and an external classification and is not stated.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 3, Theorem 1.5 (first two sentences); proof in §6.4, p. 18

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiDihedrant_Setting
open Pointwise

namespace EdgeTransBiCayley.BiDihedrant

theorem theorem_1_5 :
    (∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ D : BiCayData (DihedralGroup n),
      D.graph.Connected → IsSemisymmetric D.graph → ∀ v, 6 ≤ D.graph.degree v) ∧
    (∀ k : ℕ, Odd k → 3 ≤ k →
      ∃ (n : ℕ) (hn : NeZero n),
        letI := hn
        ∃ D : BiCayData (DihedralGroup n),
          3 ≤ n ∧ D.graph.Connected ∧ IsSemisymmetric D.graph ∧
          ∀ v, D.graph.degree v = 2 * k) := by sorry

end EdgeTransBiCayley.BiDihedrant
