-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_faithful_on_pure_braids
-- name    : BraidsLinksMCG.artin_faithful_on_pure_braids
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-14T11:52:41.342717+00:00
-- url     : https://prove2.me/theorems/2298f874-0545-47ea-b705-2ba88c6e2c91
-- title:
--   The Artin representation is faithful on pure braids
-- statement:
--   This is the substantive half of the faithfulness of the Artin representation.
--
--   Let $\xi : B_n \to \operatorname{Aut}(F_n)$ be the Artin representation, given on the generators by equation (1-14),
--
--   $$\xi(\sigma_i) : x_i \mapsto x_i x_{i+1} x_i^{-1}, \qquad x_{i+1} \mapsto x_i, \qquad x_k \mapsto x_k\ (k \neq i, i+1),$$
--
--   and let $\pi : B_n \to \Sigma_n$ be the homomorphism sending $\sigma_i$ to the transposition $(i,i+1)$, whose kernel is the pure braid group $P_n$. The assertion is that a **pure** braid acting trivially on the free group is trivial: if $\beta \in B_n$ satisfies
--
--   $$\xi(\beta) = \mathrm{id}_{F_n} \quad\text{and}\quad \pi(\beta) = \mathrm{id},$$
--
--   then $\beta = 1$.
--
--   Together with the fact that the underlying permutation of a braid can be recovered from its action on $F_n$, this yields the injectivity of $\xi$ on all of $B_n$, i.e. Corollary 1.8.3: a braid is completely determined by the automorphism of the free group it induces. Restricting attention to pure braids is what makes the statement amenable to the inductive treatment of $P_n$ furnished by the Fadell-Neuwirth fibrations and the semidirect-product decomposition of Corollary 1.8.1.
--
--   **Formalization Note** The representation $\xi$ and the permutation homomorphism $\pi$ are supplied as hypotheses together with their values on the Artin generators, which determine them uniquely. The hypothesis $\pi(\beta) = \mathrm{id}$ expresses that $\beta$ lies in the pure braid subgroup.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, Corollary 1.8.3, p. 25 (faithfulness of the representation (1-14)), restricted to the pure braid group of Corollary 1.8.1, p. 24

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_faithful_on_pure_braids (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i))
    (b : ArtinBraidGroup n) (hb : xi b = 1) (hperm : pi b = 1) : b = 1 := by sorry

end BraidsLinksMCG
