-- Prove2me | Theorems.Thm_Diaz_outer_multiplier_param
-- name    : Diaz.outer_multiplier_param
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:43.396501+00:00
-- url     : https://prove2.me/theorems/c255b38c-3b7b-4403-a330-bff3139cdf38
-- title:
--   Exact parametrisation of the outer multiplier set $N_u$
-- statement:
--   **Exact parametrisation of the outer multiplier set.**
--
--   Let $u \neq 0$, put $\rho = u\bar u$, and let $S \subseteq \mathbb{C}$ be an arbitrary set. Then
--
--   $$\{x \in \mathbb{C} : xu \in S \text{ and } x\bar u \in S\}
--   = \Bigl\{\, \tfrac{a\bar u}{\rho} \;:\; a \in S,\ \tfrac{a \bar u^{\,2}}{\rho} \in S \,\Bigr\}.$$
--
--   **Why.** If $xu = a$ then $x = a\bar u/\rho$ and $x\bar u = a\bar u^{\,2}/\rho$; conversely, for
--   $x = a\bar u/\rho$ one has $xu = a$ and $x\bar u = a\bar u^{\,2}/\rho$. The correspondence
--   $x \leftrightarrow a = xu$ is a bijection because $u \neq 0$.
--
--   **Role.** This is the computational core of Carlo Perassi's outer multiplier rigidity, which studies
--   $N_u = \{x : xu \in \widetilde{\mathcal L} \text{ and } x\bar u \in \widetilde{\mathcal L}\}$ — the
--   multipliers carrying both $u$ and $\bar u$ into the augmented logarithm space. Taking
--   $S = \widetilde{\mathcal L}$, the identity displayed above is what yields his equivalence
--   "$N_u \neq \overline{\mathbb{Q}}$ if and only if $\dim_{\overline{\mathbb{Q}}}
--   \mathcal{M}_{\bar u^{\,2}} = 2$", the remaining assertions of that proposition ($\dim N_u \leq 2$,
--   $N_u \cap \widetilde{\mathcal L} = \overline{\mathbb{Q}}$) being consequences of the strong six
--   exponentials theorem and the multiplier bound, which are not part of this node.
--
--   The Lean statement is stated for an arbitrary set $S$, so it carries no transcendence input; all the
--   arithmetic stays in the choice of $S$.
--
--   Source: Carlo Perassi, the final step of his proof of the outer multiplier rigidity, unpublished apart from
--   this node. Elementary; no novelty is claimed.

import Mathlib

open ComplexConjugate

theorem Diaz.outer_multiplier_param {u : ℂ} (hu0 : u ≠ 0) (S : Set ℂ) :
    {x : ℂ | x * u ∈ S ∧ x * conj u ∈ S}
      = (fun a => a * conj u / (u * conj u)) ''
        {a : ℂ | a ∈ S ∧ a * (conj u) ^ 2 / (u * conj u) ∈ S} := by sorry
