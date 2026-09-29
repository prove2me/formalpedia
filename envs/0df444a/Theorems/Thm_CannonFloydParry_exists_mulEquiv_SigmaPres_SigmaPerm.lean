-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mulEquiv_SigmaPres_SigmaPerm
-- name    : CannonFloydParry.exists_mulEquiv_SigmaPres_SigmaPerm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:27:12.327098+00:00
-- url     : https://prove2.me/theorems/4319469f-4eb4-45b2-af7d-ea3c76ca9abf
-- title:
--   p. 247 — the presentation of the finitary symmetric group $\Sigma$
-- statement:
--   Let $\Sigma$ be the group of permutations of $\mathbf{N} = \{0, 1, 2, \dots\}$ with finite support, and $s_i \in \Sigma$ the transposition of $i$ and $i + 1$. The group presented by generators $s_0, s_1, s_2, \dots$ and relators $s_i^2$ for all $i$, $(s_is_{i+1})^3$ for all $i$, and $(s_is_j)^2$ for all $i$ and all $j \ge i + 2$ is isomorphic to $\Sigma$, by an isomorphism sending each generator $s_i$ to the transposition $s_i$.
--
--   **Formalization Note.** The source writes "$\Sigma = \langle \dots \rangle$"; the equality is formalized as an isomorphism from the presented group that is the identity on generators.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 247, before Lemma 6.7

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem exists_mulEquiv_SigmaPres_SigmaPerm :
    ∃ e : SigmaPres ≃* SigmaPerm, ∀ i, e (PresentedGroup.of i) = sigmaGen i := by
  sorry

end CannonFloydParry
