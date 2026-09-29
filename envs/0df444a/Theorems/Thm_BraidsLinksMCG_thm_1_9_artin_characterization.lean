-- Prove2me | Theorems.Thm_BraidsLinksMCG_thm_1_9_artin_characterization
-- name    : BraidsLinksMCG.thm_1_9_artin_characterization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T19:01:57.743928+00:00
-- url     : https://prove2.me/theorems/3a0a03dd-ee9b-4c58-9adc-210457d1685f
-- title:
--   Theorem 1.9 (Artin, 1925): which endomorphisms of $F_n$ are braid automorphisms
-- statement:
--   **Theorem 1.9 (Artin, 1925).** Let $F_n = \langle x_1, \dots, x_n \rangle$ be free of rank $n$ and
--   let $\beta$ be an endomorphism of $F_n$. Then $\beta$ belongs to $B_n \subset \mathrm{Aut}\,F_n$
--   — that is, $\beta$ is the automorphism induced by some braid under the Artin representation — if
--   and only if
--
--   $$(x_i)\beta = A_i\, x_{\mu_i}\, A_i^{-1} \quad (1 \le i \le n), \qquad
--     (x_1x_2\cdots x_n)\beta = x_1x_2\cdots x_n,$$
--
--   where $(\mu_1, \dots, \mu_n)$ is a permutation of $(1, \dots, n)$ and each $A_i$ is a word in the
--   generators. In words: an endomorphism is a braid automorphism exactly when it permutes the
--   generators up to conjugacy and fixes the product $x_1x_2\cdots x_n$.
--
--   The representation $\xi$ is taken as a hypothesis: the statement is made for any homomorphism
--   from $B_n$ to $\mathrm{Aut}\,F_n$ whose value on each $\sigma_i$ is the endomorphism (1-14).
--   Corollary 1.8.3 guarantees that at least one such $\xi$ exists, so the statement is not vacuous.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, p. 30, Theorem 1.9 [Artin, 1925], conditions (1-22) and (1-23)

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem thm_1_9_artin_characterization (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n)) :
    (∃ b : ArtinBraidGroup n, ∀ w : FreeGroup (Fin n), xi b w = beta w) ↔
      ((∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
            ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹) ∧
        beta (freeWordProd n) = freeWordProd n) := by sorry

end BraidsLinksMCG
