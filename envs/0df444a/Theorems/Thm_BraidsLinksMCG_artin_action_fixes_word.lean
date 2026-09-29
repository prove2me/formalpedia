-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_action_fixes_word
-- name    : BraidsLinksMCG.artin_action_fixes_word
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-14T12:16:16.844049+00:00
-- url     : https://prove2.me/theorems/cd9c71a7-4f12-4a85-8102-b4ede3488bc7
-- title:
--   A braid automorphism fixes $x_1x_2\cdots x_n$
-- statement:
--   This is the second of the two conditions in Artin's characterization of braid automorphisms.
--
--   Let $F_n = \langle x_1,\dots,x_n\rangle$ and let $\xi : B_n \to \operatorname{Aut}(F_n)$ be the Artin representation, determined on the generators by equation (1-14),
--
--   $$\xi(\sigma_i) : x_i \mapsto x_i x_{i+1} x_i^{-1}, \qquad x_{i+1} \mapsto x_i, \qquad x_k \mapsto x_k\ \ (k \neq i, i+1).$$
--
--   The assertion is that every braid automorphism fixes the product of all the generators, taken in increasing order:
--
--   $$\xi(\beta)\bigl(x_1x_2\cdots x_n\bigr) = x_1x_2\cdots x_n \qquad \text{for all } \beta \in B_n.$$
--
--   Topologically the word $x_1x_2\cdots x_n$ represents a loop encircling all $n$ punctures, which a braid must carry to itself; algebraically the identity already holds on each generator, because replacing the two adjacent factors $x_ix_{i+1}$ by $(x_ix_{i+1}x_i^{-1})(x_i)$ leaves the product unchanged. This is condition (ii) of Theorem 1.9; together with the conjugacy condition (i) it constitutes the necessity half of Artin's characterization.
--
--   **Formalization Note** The representation $\xi$ is supplied as a hypothesis together with its values on the Artin generators, which determine it uniquely; $x_1x_2\cdots x_n$ is the ordered product of the free generators indexed by $\mathrm{Fin}\,n$.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, equation (1-14), p. 25, and Theorem 1.9, condition (ii), p. 30

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_action_fixes_word (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (b : ArtinBraidGroup n) : xi b (freeWordProd n) = freeWordProd n := by sorry

end BraidsLinksMCG
