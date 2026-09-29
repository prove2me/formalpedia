-- Prove2me | Theorems.Thm_BraidsLinksMCG_thm_1_9_sufficiency
-- name    : BraidsLinksMCG.thm_1_9_sufficiency
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-14T12:16:20.351834+00:00
-- url     : https://prove2.me/theorems/dabe1314-e386-4890-8550-7953b2b8ec7f
-- title:
--   Theorem 1.9, sufficiency: an endomorphism satisfying (i) and (ii) is a braid automorphism
-- statement:
--   This is the substantive half of Theorem 1.9, Artin's algebraic characterization of the braid automorphisms.
--
--   Let $F_n = \langle x_1,\dots,x_n\rangle$ and let $\xi : B_n \to \operatorname{Aut}(F_n)$ be the Artin representation given on the generators by equation (1-14). Let $\beta$ be an endomorphism of $F_n$ satisfying the two Artin conditions:
--
--   1. there are a permutation $\mu$ of $\{1,\dots,n\}$ and words $A_1,\dots,A_n \in F_n$ with
--   $$\beta(x_i) = A_i\, x_{\mu(i)}\, A_i^{-1} \qquad (1 \le i \le n);$$
--   2. $\beta$ fixes the product of all the generators,
--   $$\beta(x_1x_2\cdots x_n) = x_1x_2\cdots x_n .$$
--
--   Then $\beta$ is induced by a braid: there is $\beta' \in B_n$ with $\xi(\beta') = \beta$ as maps on $F_n$.
--
--   Together with the necessity of the two conditions this identifies the image of $\xi$ exactly, and hence describes the braid group as a concrete subgroup of $\operatorname{Aut}(F_n)$. It is the algebraic engine behind the treatment of the conjugacy problem and of the Magnus representations.
--
--   **Formalization Note** The representation $\xi$ is supplied as a hypothesis together with its values on the Artin generators, which determine it uniquely. The conclusion asserts the existence of a braid whose associated automorphism agrees with $\beta$ on every word; no injectivity is claimed here.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, Theorem 1.9, p. 30 (Artin, 1925), sufficiency direction; equation (1-14), p. 25

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem thm_1_9_sufficiency (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ b : ArtinBraidGroup n, ∀ w : FreeGroup (Fin n), xi b w = beta w := by sorry

end BraidsLinksMCG
