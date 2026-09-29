-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_conjugator_norm_reduction
-- name    : BraidsLinksMCG.artin_conjugator_norm_reduction
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:24:50.799736+00:00
-- url     : https://prove2.me/theorems/d0c629be-6eed-4744-a23a-2a3b800589fb
-- title:
--   A non-permutation braid automorphism can be shortened
-- statement:
--   The single inductive step in Artin's characterisation theorem: if a braid automorphism is not already a permutation of the generators, some braid strictly shortens it.
--
--   Let $\beta$ be an endomorphism of $F_n$ sending each generator to a conjugate of a generator and fixing $x_1 x_2 \cdots x_n$, and suppose $\beta$ is not of the form $x_i \mapsto x_{\nu(i)}$. Then there is a braid $c$ with
--
--   $$\sum_{i} \bigl\| \xi(c)\bigl(\beta(x_i)\bigr) \bigr\| \;<\; \sum_{i} \bigl\| \beta(x_i) \bigr\|,$$
--
--   where $\|\cdot\|$ is `FreeGroup.norm`, the length of the reduced word.
--
--   Everything else in the theorem is already discharged. The surrounding induction is proved: composing with a braid preserves both hypotheses, so the statement above can be applied repeatedly, and the process terminates because the measure is a natural number that strictly decreases. When it terminates, $\beta$ has become a permutation automorphism, which is the conclusion of `BraidsLinksMCG.artin_conjugators_trivializable`; that in turn yields `BraidsLinksMCG.thm_1_9_sufficiency`, where the permutation is forced to be the identity because a positive word is reduced.
--
--   So this is the only remaining content, and it is where the cancellation analysis lives.
--
--   The classical argument runs as follows. Write $\beta(x_i) = A_i x_{\mu(i)} A_i^{-1}$. The hypothesis that $\beta$ fixes $x_1 \cdots x_n$ says that
--
--   $$A_1 x_{\mu(1)} A_1^{-1} \, A_2 x_{\mu(2)} A_2^{-1} \cdots A_n x_{\mu(n)} A_n^{-1}$$
--
--   collapses to a reduced word of length $n$. Since the displayed product has length $\sum_i (2\|A_i\| + 1)$ before reduction, the cancellation is forced to be extensive, and it can only occur between the tail $A_i^{-1}$ of one factor and the head $A_{i+1}$ of the next. Examining the possibilities at the first index where some $A_i$ is nontrivial produces an adjacent pair of strands whose half-twist, applied on the left, cancels a letter from the relevant conjugator; that is the required $c$, taken to be $\sigma_j^{\pm 1}$ for a suitable $j$ and sign.
--
--   A word on the choice of measure. The conjugators $A_i$ are not canonical --- each is determined only up to right multiplication by a power of $x_{\mu(i)}$ --- so "total conjugator length" is not well defined without fixing representatives. The total reduced length of the images $\beta(x_i)$ is canonical and decreases in step with it, which is why it is used here. Note also that the hypothesis is stated as "not a permutation automorphism" rather than as a numerical condition on the measure; this avoids having to argue separately that minimal measure forces the conjugators to vanish.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, Theorem 1.9; Artin, Theory of braids, Ann. of Math. 48 (1947), the length-reduction step.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_conjugator_norm_reduction (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hword : beta (freeWordProd n) = freeWordProd n)
    (hnotperm : ¬ ∃ nu : Equiv.Perm (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = FreeGroup.of (nu i)) :
    ∃ c : ArtinBraidGroup n,
      (∑ i : Fin n, FreeGroup.norm (((xi c).toMonoidHom.comp beta) (FreeGroup.of i)))
        < ∑ i : Fin n, FreeGroup.norm (beta (FreeGroup.of i)) := by sorry

end BraidsLinksMCG
