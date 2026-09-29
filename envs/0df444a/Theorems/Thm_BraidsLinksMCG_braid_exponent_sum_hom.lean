-- Prove2me | Theorems.Thm_BraidsLinksMCG_braid_exponent_sum_hom
-- name    : BraidsLinksMCG.braid_exponent_sum_hom
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-14T12:08:44.341933+00:00
-- url     : https://prove2.me/theorems/168ee371-649c-495f-a88c-d73aa165df43
-- title:
--   The exponent-sum homomorphism $B_n \to \mathbb{Z}$
-- statement:
--   The exponent sum of a braid word is an invariant of the braid.
--
--   Let $B_n$ be the abstract braid group with Artin generators $\sigma_1,\dots,\sigma_{n-1}$ and the defining relations
--
--   $$\sigma_i\sigma_j=\sigma_j\sigma_i\ (|i-j|\ge 2),\qquad \sigma_i\sigma_{i+1}\sigma_i=\sigma_{i+1}\sigma_i\sigma_{i+1}.$$
--
--   The assertion is that there is a group homomorphism
--
--   $$\varepsilon : B_n \longrightarrow \mathbb{Z}, \qquad \varepsilon(\sigma_i) = 1 \quad \text{for every } i,$$
--
--   so that the number of positive crossings minus the number of negative crossings in a braid word depends only on the braid it represents. Both families of defining relations preserve the number of letters counted with sign, which is what makes the assignment well defined.
--
--   The homomorphism $\varepsilon$ is the abelianization map of $B_n$: since all generators are conjugate, any homomorphism to an abelian group factors through it. It is the standard device for showing that a given braid is non-trivial, or that an element has infinite order, and it is used in particular for the generator of the centre of $B_n$.
--
--   **Formalization Note** Braid generators are indexed by $\mathrm{Fin}(n-1)$ with truncated subtraction, so there are no generators when $n \le 1$. The target group $\mathbb{Z}$ is written multiplicatively, and $\varepsilon(\sigma_i)$ is the element corresponding to the integer $1$.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, relations (1-1) and (1-2), p. 11; the exponent sum is used in the discussion of the centre, Corollary 1.8.4, p. 28

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem braid_exponent_sum_hom (n : ℕ) :
    ∃ eps : ArtinBraidGroup n →* Multiplicative ℤ,
      ∀ i : Fin (n - 1), eps (sigma i) = Multiplicative.ofAdd (1 : ℤ) := by sorry

end BraidsLinksMCG
