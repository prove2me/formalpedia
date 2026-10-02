-- Prove2me | Theorems.Thm_BurauFaithful_normal_subgroup_dichotomy
-- name    : BurauFaithful.normal_subgroup_dichotomy
-- status  : Disproved
-- author  : @junyihjy
-- created : 2026-09-24T13:57:01.040988+00:00
-- url     : https://prove2.me/theorems/cda1a80c-9872-4b26-ae23-6c3464ce1319
-- title:
--   Normal subgroups of the braid group are central or contain the commutator subgroup
-- statement:
--   **Normal-subgroup dichotomy for braid groups (Long's theorem).** Let $n$ be a natural number and $K$ a normal subgroup of the braid group $B_n$. Then either $K$ is contained in the centre $Z(B_n)$, or $K$ contains the commutator subgroup $[B_n, B_n]$. For $n \le 2$ the group $B_n$ is abelian, so the first alternative always holds and the statement is vacuous; the content is for $n \ge 3$. This is the structural input behind Long's criterion: applied to $K = \ker \rho_n$ and to the noncentral normal subgroup $N$, it forces either $\ker\rho_n \le Z(B_n)$ or $[B_n,B_n] \le \ker\rho_n \cap N$. References: D. D. Long, *A note on the normal subgroups of mapping class groups*, Math. Proc. Cambridge Philos. Soc. 99 (1986), Theorem 2.2; E. A. Gorin and V. Ya. Lin, *Algebraic equations with continuous coefficients and some problems of the algebraic theory of braids*, Math. USSR-Sb. 7 (1969) (the $n \ge 5$ case; $n = 3, 4$ by the same method).
-- source:
--   D. D. Long, A note on the normal subgroups of mapping class groups, Math. Proc. Cambridge Philos. Soc. 99 (1986), Theorem 2.2; Gorin-Lin, Math. USSR-Sb. 7 (1969). Structural input for Long's criterion (BurauFaithful.burau_faithful_of_faithful_on_normal, node 906aaa4a-93c6-4fbf-862e-71e93ea21242), quoted in the introduction of arXiv:2607.05283v2.

import Definitions.Def_BurauFaithful_UnreducedBurau
set_option autoImplicit false

namespace BurauFaithful

theorem normal_subgroup_dichotomy (n : ℕ) (K : Subgroup (BraidsLinksMCG.ArtinBraidGroup n))
    [K.Normal] :
    K ≤ Subgroup.center (BraidsLinksMCG.ArtinBraidGroup n) ∨
      commutator (BraidsLinksMCG.ArtinBraidGroup n) ≤ K := by sorry

end BurauFaithful
