-- Prove2me | Theorems.Thm_BraidsLinksMCG_braid_perm_hom
-- name    : BraidsLinksMCG.braid_perm_hom
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-14T11:52:31.386149+00:00
-- url     : https://prove2.me/theorems/e2ab2ce5-30d9-4d01-a723-8ed5556d822a
-- title:
--   The natural homomorphism $B_n \to \Sigma_n$ sending $\sigma_i$ to a transposition
-- statement:
--   Every braid has an underlying permutation of its $n$ strands, and this assignment is a group homomorphism.
--
--   Let $B_n$ be the abstract braid group with Artin generators $\sigma_1,\dots,\sigma_{n-1}$ and defining relations
--
--   $$\sigma_i\sigma_j=\sigma_j\sigma_i\ (|i-j|\ge 2),\qquad \sigma_i\sigma_{i+1}\sigma_i=\sigma_{i+1}\sigma_i\sigma_{i+1},$$
--
--   and let $\Sigma_n$ be the symmetric group on the strand labels $\{1,\dots,n\}$. The assertion is that there exists a group homomorphism
--
--   $$\pi : B_n \longrightarrow \Sigma_n, \qquad \pi(\sigma_i) = (i,\ i+1),$$
--
--   sending each elementary braid to the transposition of the two strands it interchanges. Equivalently, the transpositions $(i,i+1)$ satisfy Artin's two families of relations in $\Sigma_n$, so the assignment on generators extends to the whole group.
--
--   This homomorphism is the algebraic counterpart of the map that records, for a motion of $n$ points of the plane, the permutation by which the points are rearranged; its kernel is the pure braid group. It is the basic tool for separating a braid's combinatorial shadow from its genuinely braided content, and it is used whenever a statement about $B_n$ is reduced to the corresponding statement about pure braids.
--
--   **Formalization Note** Braid generators are indexed by $\mathrm{Fin}(n-1)$ with truncated subtraction, the index $i$ standing for the book's $\sigma_{i+1}$; `strandIdx i` and `strandIdxSucc i` are the two strand labels $i$ and $i+1$ in $\mathrm{Fin}\,n$ that the generator interchanges. The statement is existential because the homomorphism is being constructed, and it is pinned down uniquely by its values on the generators, which generate the group.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, Proposition 1.1 and the discussion of the permutation associated with a braid, pp. 11-13; relations (1-1) and (1-2), p. 11

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem braid_perm_hom (n : ℕ) :
    ∃ pi : ArtinBraidGroup n →* Equiv.Perm (Fin n),
      ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i) := by sorry

end BraidsLinksMCG
