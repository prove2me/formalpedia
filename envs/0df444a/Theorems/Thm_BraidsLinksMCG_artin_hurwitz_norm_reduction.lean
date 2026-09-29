-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_hurwitz_norm_reduction
-- name    : BraidsLinksMCG.artin_hurwitz_norm_reduction
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T23:57:43.060148+00:00
-- url     : https://prove2.me/theorems/852cceb4-8489-415d-b1eb-6ca2fb1d17db
-- title:
--   Hurwitz-form length reduction for Artin's characterization
-- statement:
--   Let $\xi$ be the Artin action of $B_n$ on the free group $F_n = \langle x_1,\dots,x_n\rangle$, pinned on generators by $\xi(\sigma_i) = $ `artinEndo n i`. Let $\beta$ be an endomorphism of $F_n$ which sends every generator to a conjugate of a generator, following some permutation $\mu$,
--   $$\beta(x_i) = A_i\, x_{\mu(i)}\, A_i^{-1},$$
--   and which fixes the word $x_1x_2\cdots x_n$. If $\beta$ is not already a permutation map $x_i \mapsto x_{\nu(i)}$, then some braid $c$ makes the composite $\beta \circ \xi(c)$ strictly shorter:
--   $$\sum_{i=1}^{n} \bigl\lVert \beta(\xi(c)(x_i)) \bigr\rVert \;<\; \sum_{i=1}^{n} \bigl\lVert \beta(x_i) \bigr\rVert,$$
--   the norm being the length of the reduced word.
--
--   This is the descent step in Artin's characterization of the braid automorphisms. Iterating it terminates, at which point $\beta \circ \xi(c)$ is a permutation map; since both $\beta$ and $\xi(c)$ fix $x_1\cdots x_n$, that permutation map fixes it too and is therefore the identity, so $\beta = \xi(c)^{-1}$ lies in the image of $\xi$.
--
--   **The composition order is the whole point.** Write $w_i = \beta(x_i)$. The hypotheses say exactly that $(w_1,\dots,w_n)$ is an $n$-tuple of conjugates of generators with $w_1w_2\cdots w_n = x_1\cdots x_n$. Because $\xi(\sigma_k)$ sends $x_k \mapsto x_kx_{k+1}x_k^{-1}$ and $x_{k+1}\mapsto x_k$, right-composition replaces that tuple by
--   $$(w_1,\dots,w_{k-1},\; w_kw_{k+1}w_k^{-1},\; w_k,\; w_{k+2},\dots,w_n),$$
--   which is the Hurwitz move of the braid group on such tuples; $\xi(\sigma_k^{-1})$ gives the inverse move $(\dots, w_{k+1}, w_{k+1}^{-1}w_kw_{k+1},\dots)$. Only two entries change, so for $c=\sigma_k^{\pm 1}$ the inequality collapses to a single local comparison,
--   $$\lVert w_kw_{k+1}w_k^{-1}\rVert < \lVert w_{k+1}\rVert \qquad\text{resp.}\qquad \lVert w_{k+1}^{-1}w_kw_{k+1}\rVert < \lVert w_k\rVert ,$$
--   and the task is to locate an adjacent pair where the conjugation cancels. The classical argument produces such a $k$, so the statement is expected to hold with $c$ an elementary generator; it is stated for a general $c$ only because that is all the descent needs.
--
--   Left-composition, $\xi(c)\circ\beta$, is a different operation: it applies one automorphism to all $n$ words simultaneously and changes every entry of the tuple at once, so it offers no local handle of this kind. The two versions are equally true, since both follow once the characterization theorem is known, but only this one turns the descent into a finite cancellation question about a single adjacent pair.
--
--   The hypothesis that $\beta$ is not a permutation map is what rules out the fixed point of the descent: if all $A_i$ can be taken trivial the total length is already $n$, its minimum, and no move decreases it.
-- source:
--   Artin, Theory of braids, Ann. of Math. 48 (1947), Section 1; Birman, Braids, Links and Mapping Class Groups, Theorem 1.9; Kassel-Turaev, Braid Groups, Theorem 1.17 and the Hurwitz action of B_n on tuples of conjugates of the generators.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_hurwitz_norm_reduction (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hword : beta (freeWordProd n) = freeWordProd n)
    (hnotperm : ¬ ∃ nu : Equiv.Perm (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = FreeGroup.of (nu i)) :
    ∃ c : ArtinBraidGroup n,
      (∑ i : Fin n, FreeGroup.norm (beta (xi c (FreeGroup.of i))))
        < ∑ i : Fin n, FreeGroup.norm (beta (FreeGroup.of i)) := by sorry

end BraidsLinksMCG
