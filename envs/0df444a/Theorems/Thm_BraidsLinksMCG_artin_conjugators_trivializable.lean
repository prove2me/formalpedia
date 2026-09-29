-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_conjugators_trivializable
-- name    : BraidsLinksMCG.artin_conjugators_trivializable
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T20:29:12.507335+00:00
-- url     : https://prove2.me/theorems/b67e13d1-718f-4071-8b9e-a2b782488833
-- title:
--   A braid automorphism can be normalised to a permutation
-- statement:
--   The combinatorial heart of Artin's characterisation theorem: a braid automorphism of the free group can be normalised, by composing with a braid, so that its conjugators disappear.
--
--   Precisely, let $\beta$ be an endomorphism of $F_n$ sending each generator to a conjugate of a generator,
--
--   $$\beta(x_i) = A_i\, x_{\mu(i)}\, A_i^{-1},$$
--
--   and fixing the word $x_1 x_2 \cdots x_n$. The claim is that there is a braid $b$ such that the composite $\xi(b) \circ \beta$ sends every generator to a bare generator: $\xi(b)(\beta(x_i)) = x_{\nu(i)}$ for some permutation $\nu$, with no conjugator left.
--
--   This isolates the only hard step in Teorema 1.9. Once the conjugators are gone the rest is immediate and is already carried out in the parent submission: the normalised map still fixes $x_1 \cdots x_n$, because braids fix that word and $\beta$ was assumed to; evaluating the fixing on the explicit product shows $x_{\nu(1)} \cdots x_{\nu(n)} = x_1 \cdots x_n$; since both sides are positive words they are reduced, so the letters match and $\nu$ is the identity; hence $\xi(b) \circ \beta$ is the identity on generators and therefore everywhere, giving $\beta = \xi(b^{-1})$.
--
--   The classical argument for the normalisation is an induction on the total reduced length of the images $\beta(x_i)$. The hypothesis that $\beta$ fixes $x_1 \cdots x_n$ is what drives it: the product
--
--   $$A_1 x_{\mu(1)} A_1^{-1} \, A_2 x_{\mu(2)} A_2^{-1} \cdots A_n x_{\mu(n)} A_n^{-1}$$
--
--   has to collapse to a reduced word of length $n$, which forces heavy cancellation between consecutive factors $A_i^{-1} A_{i+1}$. Analysing where that cancellation can occur produces an adjacent pair on which some $\sigma_i^{\pm 1}$ can be applied to shorten the total length, and the induction closes when every conjugator is trivial.
--
--   Note the statement deliberately avoids naming a length measure. The conjugators $A_i$ are not canonical --- each is determined only up to right multiplication by a power of $x_{\mu(i)}$ --- so a formulation quantifying over "the" total conjugator length would have to fix representatives first. Asking instead for the existence of a normalising braid says the same thing without that bookkeeping, and is what the surrounding proof actually consumes.
--
--   No claim is made that $b$ is unique, and none is needed.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, Theorem 1.9; Artin, Theory of braids, Ann. of Math. 48 (1947).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_conjugators_trivializable (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ b : ArtinBraidGroup n, ∃ nu : Equiv.Perm (Fin n),
      ∀ i : Fin n, xi b (beta (FreeGroup.of i)) = FreeGroup.of (nu i) := by sorry

end BraidsLinksMCG
