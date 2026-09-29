-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_action_conj_perm
-- name    : BraidsLinksMCG.artin_action_conj_perm
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-14T11:52:32.685855+00:00
-- url     : https://prove2.me/theorems/749829d1-e2a2-47b8-970a-eb4bec29ddcb
-- title:
--   A braid automorphism sends $x_j$ to a conjugate of $x_{\mu(j)}$
-- statement:
--   This is the first of the two conditions in Artin's characterization of braid automorphisms.
--
--   Let $F_n = \langle x_1,\dots,x_n\rangle$ be the free group of rank $n$, let $\xi : B_n \to \operatorname{Aut}(F_n)$ be the Artin representation, determined by its values on the generators by equation (1-14),
--
--   $$\xi(\sigma_i) : x_i \mapsto x_i x_{i+1} x_i^{-1}, \qquad x_{i+1} \mapsto x_i, \qquad x_k \mapsto x_k\ (k \neq i, i+1),$$
--
--   and let $\pi : B_n \to \Sigma_n$ be the homomorphism sending $\sigma_i$ to the transposition $(i,i+1)$. Then for every braid $\beta \in B_n$ and every index $j$ there is a word $A \in F_n$ with
--
--   $$\xi(\beta)(x_j) = A\, x_{\pi(\beta)(j)}\, A^{-1}.$$
--
--   In words: a braid automorphism permutes the conjugacy classes of the free generators, and the induced permutation of the indices is exactly the underlying permutation of the braid. This is condition (i) of Theorem 1.9 (with $\mu = \pi(\beta)$), and it is the statement that lets one read the strand permutation of a braid off its action on $F_n$; in particular a braid acting trivially on $F_n$ must be a pure braid.
--
--   **Formalization Note** The representation $\xi$ and the permutation homomorphism $\pi$ are supplied as hypotheses together with their values on the Artin generators, which determine them uniquely. Free generators are indexed by $\mathrm{Fin}\,n$ and braid generators by $\mathrm{Fin}(n-1)$.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, equation (1-14), p. 25, and Theorem 1.9, condition (i), p. 30

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_action_conj_perm (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i))
    (b : ArtinBraidGroup n) (j : Fin n) :
    ∃ A : FreeGroup (Fin n),
      xi b (FreeGroup.of j) = A * FreeGroup.of (pi b j) * A⁻¹ := by sorry

end BraidsLinksMCG
