-- Prove2me | Theorems.Thm_BurauFaithful_burau_faithful_of_faithful_on_normal
-- name    : BurauFaithful.burau_faithful_of_faithful_on_normal
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T20:48:53.166266+00:00
-- url     : https://prove2.me/theorems/906aaa4a-93c6-4fbf-862e-71e93ea21242
-- title:
--   Long's criterion: faithfulness on a nontrivial noncentral normal subgroup
-- statement:
--   **Long's criterion.** Let $n$ be a natural number and let $N$ be a subgroup of the braid group $B_n$ such that
--
--   1. $N$ is normal in $B_n$;
--   2. $N$ is nontrivial, i.e. $N \neq \{1\}$;
--   3. $N$ is not contained in the centre of $B_n$;
--   4. the Burau representation is faithful on $N$: every $x \in N$ with $\rho_n(x) = I_n$ equals $1$.
--
--   Then the Burau representation $\rho_n : B_n \to \mathrm{GL}_n(\mathbb{Z}[t,t^{-1}])$ is faithful on all of $B_n$.
--
--   The criterion is due to D. D. Long and is quoted in the introduction of the source paper; it is what allows the faithfulness question for $B_4$ to be reduced to the Brunnian subgroup $\mathrm{Brun}_4$. The statement is made for all $n$; for $n \le 2$ the braid group is abelian, so hypothesis 3 cannot be met and the assertion has no content there, the substance being the case $n \ge 3$.
-- source:
--   Vasudha Bharathram, Joan S. Birman, Tara E. Brendle, *The Burau representation is faithful for n = 4*, arXiv:2607.05283v1 (6 July 2026), https://arxiv.org/abs/2607.05283, Section 1 (strategy of proof), quoting D. D. Long, *A note on the normal subgroups of mapping class groups*, Math. Proc. Cambridge Philos. Soc. 99 (1986), Theorem 2.2

import Definitions.Def_BurauFaithful_UnreducedBurau

namespace BurauFaithful

theorem burau_faithful_of_faithful_on_normal (n : ℕ)
    (N : Subgroup (BraidsLinksMCG.ArtinBraidGroup n)) [N.Normal] (hnontrivial : N ≠ ⊥)
    (hnoncentral : ¬ N ≤ Subgroup.center (BraidsLinksMCG.ArtinBraidGroup n))
    (hfaithful : ∀ x ∈ N, burauRep n x = 1 → x = 1) : Function.Injective (burauRep n) := by sorry

end BurauFaithful
