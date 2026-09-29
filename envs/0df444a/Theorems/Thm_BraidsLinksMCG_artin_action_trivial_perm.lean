-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_action_trivial_perm
-- name    : BraidsLinksMCG.artin_action_trivial_perm
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T20:36:14.96022+00:00
-- url     : https://prove2.me/theorems/7eadec3e-76da-4607-b4f9-3174e17a5a14
-- title:
--   A braid acting trivially on $F_n$ is pure
-- statement:
--   A braid that acts trivially on the free group induces the trivial permutation of the strands.
--
--   Precisely, let $\xi$ be the Artin representation, so $\xi(\sigma_i)$ is Artin's automorphism, and let $\pi$ be the underlying-permutation homomorphism, so $\pi(\sigma_i)$ is the transposition of strands $i$ and $i+1$. If $\xi(b) = 1$ then $\pi(b) = 1$.
--
--   Equivalently: $\ker \xi \le \ker \pi$, so a braid in the kernel of the Artin representation is automatically pure.
--
--   The point of the statement is that it removes a hypothesis. Birman's inductive result on pure braids assumes both that the braid acts trivially *and* that its permutation is trivial, the second condition being what restricts attention to $P_n$ where the semidirect decomposition is available. This lemma shows the second hypothesis is redundant given the first, so faithfulness of the Artin representation follows from the pure-braid case alone, with no separate argument about permutations.
--
--   The proof is short given what is already on the platform. `BraidsLinksMCG.artin_action_conj_perm` is proved and says that for every braid $b$ and index $j$ there is a word $A$ with
--
--   $$\xi(b)(x_j) = A\, x_{\pi(b)(j)}\, A^{-1}.$$
--
--   Setting $\xi(b) = 1$ turns this into $x_j = A\, x_{\pi(b)(j)}\, A^{-1}$: the generator $x_j$ is conjugate to the generator $x_{\pi(b)(j)}$.
--
--   So everything reduces to a fact about free groups: conjugate generators are equal. That is proved here by abelianising selectively. For a fixed index $j$, send $x_j \mapsto 1 \in \mathbb{Z}$ and every other generator to $0$. Conjugation is invisible in an abelian target, so the two sides of the displayed identity have the same image; the left side has image $1$ and the right side has image $0$ unless the indices agree. Hence $\pi(b)(j) = j$ for every $j$, which is the claim.
--
--   Note the argument uses only that the target is abelian and that the chosen homomorphism separates the generator in question from all the others, so it applies verbatim to any free group on a set with decidable equality.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, around equation (1-14) and Corollary 1.8.3; the free-group input is the standard fact that conjugate generators of a free group coincide.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_action_trivial_perm (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i))
    (b : ArtinBraidGroup n) (hb : xi b = 1) : pi b = 1 := by sorry

end BraidsLinksMCG
