-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiDihedrant_proposition_6_4
-- name    : EdgeTransBiCayley.BiDihedrant.proposition_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:39:14.311533+00:00
-- url     : https://prove2.me/theorems/a4430ee3-fe8a-4742-8939-68e32838c24a
-- title:
--   Proposition 6.4 — if k is odd and λ^k ≡ −1 mod n, then Γ(n, λ, 2k) is semisymmetric
-- statement:
--   Assume the hypotheses of Example 6.2 ($n \ge 5$, $k \ge 2$, $\lambda \in \mathbb Z_n^*$ of order $2k$, $1 + \lambda^2 + \cdots + \lambda^{2(k-1)} \equiv 0 \pmod n$). If moreover $k$ is odd and
--
--   $$
--   \lambda^k \equiv -1 \pmod n,
--   $$
--
--   then $\Gamma(n,\lambda,2k)$ is semisymmetric: it has constant valency and its full automorphism group is transitive on edges but not on vertices.
--
--   Together with suitable parameters for each odd $k \ge 3$ this gives the existence half of Theorem 1.5.
--
--   **Formalization Note** "$\Gamma(n,\lambda,2k)$" in the proposition refers to the graphs of Example 6.2, so Example 6.2's hypotheses (`Ex62Hyp`) are hypotheses here. $-1$ is computed in `ZMod n`.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 13, Proposition 6.4

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiDihedrant_Gamma
open Pointwise

namespace EdgeTransBiCayley.BiDihedrant

theorem proposition_6_4 (n lam k : ℕ) [NeZero n] (h : Ex62Hyp n lam k) (hk : Odd k)
    (hlam : (lam : ZMod n) ^ k = -1) :
    IsSemisymmetric (gammaData n lam k).graph := by sorry

end EdgeTransBiCayley.BiDihedrant
